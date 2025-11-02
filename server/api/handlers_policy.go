package api

import (
    "bytes"
    "encoding/json"
    "fmt"
    "io"
    "net/http"
    "os"
    "path/filepath"

    "github.com/superfly/sprite-env/pkg/policy"
)

// Strict validation types (mirror policy JSON schema)
type policyNetworkDoc struct {
    Rules []policyRule `json:"rules"`
}

type policyRule struct {
    Domain  string `json:"domain,omitempty"`
    Action  string `json:"action,omitempty"`
    Include string `json:"include,omitempty"`
}

func validatePolicyDocStrict(data []byte) error {
    // Disallow unknown fields at all levels
    dec := json.NewDecoder(bytes.NewReader(data))
    dec.DisallowUnknownFields()
    var doc policyNetworkDoc
    if err := dec.Decode(&doc); err != nil {
        return fmt.Errorf("invalid json: %w", err)
    }
    // Require top-level rules key to be present (may be empty array)
    if doc.Rules == nil {
        return fmt.Errorf("missing required key: rules")
    }
    // Validate each rule entry strictly
    for i, r := range doc.Rules {
        hasDomain := r.Domain != ""
        hasInclude := r.Include != ""
        if hasDomain == hasInclude { // either both set or both empty -> invalid
            return fmt.Errorf("rule %d: must set exactly one of domain or include", i)
        }
        if hasInclude {
            if r.Include != "defaults" {
                return fmt.Errorf("rule %d: include must be \"defaults\"", i)
            }
            if r.Domain != "" {
                return fmt.Errorf("rule %d: domain not allowed with include", i)
            }
            if r.Action != "" && r.Action != "allow" && r.Action != "deny" {
                return fmt.Errorf("rule %d: action must be allow or deny when provided", i)
            }
        } else { // hasDomain
            if r.Action != "allow" && r.Action != "deny" {
                return fmt.Errorf("rule %d: action is required and must be allow or deny", i)
            }
            if r.Include != "" {
                return fmt.Errorf("rule %d: include not allowed with domain", i)
            }
        }
    }
    return nil
}

// HandlePolicyNetwork serves and updates the policy network.json at /policy/network
func (h *Handlers) HandlePolicyNetwork(w http.ResponseWriter, r *http.Request) {
    cfgDir := h.system.GetPolicyConfigDir()
    cfgPath := filepath.Join(cfgDir, "network.json")

    switch r.Method {
    case http.MethodGet:
        // Return current config (or empty rules if missing)
        data, err := os.ReadFile(cfgPath)
        if err != nil {
            w.Header().Set("Content-Type", "application/json")
            w.WriteHeader(http.StatusOK)
            _, _ = w.Write([]byte("{\n  \"rules\": []\n}\n"))
            return
        }
        w.Header().Set("Content-Type", "application/json")
        w.WriteHeader(http.StatusOK)
        _, _ = w.Write(data)
        return

    case http.MethodPost:
        defer r.Body.Close()
        body, err := io.ReadAll(r.Body)
        if err != nil {
            http.Error(w, "failed to read request body", http.StatusBadRequest)
            return
        }
        // Strict schema validation (no extra keys, required fields present, valid combinations)
        if err := validatePolicyDocStrict(body); err != nil {
            http.Error(w, "invalid policy config", http.StatusBadRequest)
            return
        }

        if err := os.MkdirAll(cfgDir, 0755); err != nil {
            http.Error(w, "failed to create config dir", http.StatusInternalServerError)
            return
        }

        // Validate again via policy.LoadNetworkConfig by writing to a temp dir (ensures semantic expansion succeeds)
        tmpDir, err := os.MkdirTemp("", "policy-validate-*")
        if err != nil {
            http.Error(w, "failed to create temp dir", http.StatusInternalServerError)
            return
        }
        defer os.RemoveAll(tmpDir)
        if err := os.WriteFile(filepath.Join(tmpDir, "network.json"), body, 0644); err != nil {
            http.Error(w, "failed to write temp file", http.StatusInternalServerError)
            return
        }
        if _, _, err := policy.LoadNetworkConfig(tmpDir); err != nil {
            http.Error(w, "invalid policy config", http.StatusBadRequest)
            return
        }

        // Atomic write to target
        tmpFile, err := os.CreateTemp(cfgDir, "network.json.*.new")
        if err != nil {
            http.Error(w, "failed to create temp target", http.StatusInternalServerError)
            return
        }
        tmpName := tmpFile.Name()
        if _, err := tmpFile.Write(body); err != nil {
            _ = tmpFile.Close()
            _ = os.Remove(tmpName)
            http.Error(w, "failed to write temp target", http.StatusInternalServerError)
            return
        }
        _ = tmpFile.Sync()
        _ = tmpFile.Close()

        if err := os.Rename(tmpName, cfgPath); err != nil {
            _ = os.Remove(tmpName)
            http.Error(w, "failed to install config", http.StatusInternalServerError)
            return
        }
        w.WriteHeader(http.StatusNoContent)
        return

    default:
        http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
        return
    }
}
