//go:build !netmodel && !goose

package vsrnet

// RegisterJSON registers the kit's encoding/json codec with the encoding/json model; in a real
// build, as here, it does nothing. Hand-written for now: models/json/jsongen.py would write it
// (json_real_gen.go, with the codec and the model build's registration) from json.toml, but it
// refuses go-vsr's log.Logs, which has MarshalJSON and UnmarshalJSON (notes/dsv-vr.md, "State").
func RegisterJSON() {}
