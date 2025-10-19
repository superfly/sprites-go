package api

import (
	"context"
	"net/http"
	"net/url"
	"strings"

	gorillaws "github.com/gorilla/websocket"
	"github.com/superfly/sprite-env/pkg/wss"
)

// HandleControl establishes the control websocket and registers operations.
func (h *Handlers) HandleControl(w http.ResponseWriter, r *http.Request) {
	if r.Method != http.MethodGet {
		http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
		return
	}

	// Set up wss server with exec operation registered
	router := wss.NewRouter()

	// Register exec operation using ServeExecWS
	router.Handle("exec", func(ctx context.Context, c wss.OpConn, args url.Values) error {
		// Compose URL params compatible with ServeExecWS from args
		q := url.Values{}
		for k, vs := range args {
			for _, v := range vs {
				q.Add(k, v)
			}
		}
		return h.ServeExecWS(ctx, c, q)
	})

	srv := &wss.Server{
		Router:   router,
		Upgrader: gorillaws.Upgrader{CheckOrigin: func(r *http.Request) bool { return true }},
		Logger:   h.logger,
	}

	srv.Handle(w, r)
}

// setupControlRoute adds the control route to the mux under /v1/sprites/:name/control
func (s *Server) setupControlRoute(mux *http.ServeMux) {
	mux.HandleFunc("/v1/sprites/", func(w http.ResponseWriter, r *http.Request) {
		// match /v1/sprites/:name/control
		parts := strings.Split(strings.Trim(r.URL.Path, "/"), "/")
		if len(parts) == 4 && parts[0] == "v1" && parts[1] == "sprites" && parts[3] == "control" {
			s.handlers.HandleControl(w, r)
			return
		}
		http.NotFound(w, r)
	})
}
