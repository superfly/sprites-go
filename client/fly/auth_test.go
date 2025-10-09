package fly

import (
	"testing"
)

func TestIsMacaroon(t *testing.T) {
	tests := []struct {
		name  string
		token string
		want  bool
	}{
		{
			name:  "macaroon v1 restricted",
			token: "fm1r_sometoken",
			want:  true,
		},
		{
			name:  "macaroon v2",
			token: "fm2_sometoken",
			want:  true,
		},
		{
			name:  "bearer token",
			token: "fo1_sometoken",
			want:  false,
		},
		{
			name:  "plain token",
			token: "sometokenstring",
			want:  false,
		},
		{
			name:  "multiple tokens with macaroon",
			token: "fm1r_token1,fm2_token2",
			want:  true,
		},
		{
			name:  "multiple tokens without macaroon",
			token: "fo1_token1,fo2_token2",
			want:  false,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			if got := IsMacaroon(tt.token); got != tt.want {
				t.Errorf("IsMacaroon(%q) = %v, want %v", tt.token, got, tt.want)
			}
		})
	}
}

func TestAuthorizationHeader(t *testing.T) {
	tests := []struct {
		name  string
		token string
		want  string
	}{
		{
			name:  "macaroon v1",
			token: "fm1r_sometoken",
			want:  "FlyV1 fm1r_sometoken",
		},
		{
			name:  "macaroon v2",
			token: "fm2_sometoken",
			want:  "FlyV1 fm2_sometoken",
		},
		{
			name:  "bearer token",
			token: "sometoken",
			want:  "Bearer sometoken",
		},
		{
			name:  "multiple tokens with macaroon",
			token: "fm1r_token1,fm2_token2",
			want:  "FlyV1 fm1r_token1,fm2_token2",
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			if got := AuthorizationHeader(tt.token); got != tt.want {
				t.Errorf("AuthorizationHeader(%q) = %q, want %q", tt.token, got, tt.want)
			}
		})
	}
}
