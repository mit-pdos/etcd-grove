// Package jsonpkgtest: types for jsongen's same-package mode (models/json/jsongen_core.py, THE
// SAME-PACKAGE METHODS; mit-pdos/etcd-grove#24, J3). json.toml's roots get the generated methods
// (json_model_gen.go, a model build's); dispatch_test.go checks, in the real build and in the
// encoding/json model's (run.sh in internal/jsonstreamtest... see dispatch_test.go), that
// Marshal, Unmarshal and Encoder.Encode give the same results.
package jsonpkgtest

// Attrs is embedded in Rec (its fields promoted), as membership's RaftAttributes in Member.
type Attrs struct {
	URLs    []string `json:"urls,omitempty"`
	Learner bool     `json:"isLearner,omitempty"`
}

// Rec is a root: an embedded struct, a pointer field and an unexported field (ignored).
type Rec struct {
	ID uint64 `json:"id"`
	Attrs
	Name  string  `json:"name"`
	Next  *Attrs  `json:"next,omitempty"`
	hidden int
}

// Ctx embeds Rec and is a root itself (its own methods shadow Rec's), as ConfigChangeContext.
type Ctx struct {
	Rec
	Promote bool `json:"isPromote"`
}

// Wrap embeds Rec and is not a root: it has Rec's methods by promotion, so the model's dispatch
// reaches Rec's methods with a Wrap, which are not modelled there (a panic); real encoding/json
// encodes it by its own structure.
type Wrap struct {
	Rec
	Extra int `json:"extra"`
}

// token is an unexported root (as k8s's storage.continueToken).
type token struct {
	Version string `json:"v"`
	Rev     int64  `json:"rv"`
}

// NewToken returns a token (for the tests).
func NewToken(v string, r int64) any { return token{Version: v, Rev: r} }

// TokenPtr returns a *token (for the tests).
func TokenPtr() any { return &token{} }
