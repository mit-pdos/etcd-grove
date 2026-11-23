//go:build goose

package vsrnet

// RegisterJSON, as Goose translates it: a placeholder until models/json/jsongen.py writes the
// kit's codec and its registration with the encoding/json model (json_model_gen.go); it refuses
// go-vsr's log.Logs, which has MarshalJSON and UnmarshalJSON. The translation's encoding/json is
// the main tree's names-only one, and the proof takes encoding/json's specs as hypotheses
// (notes/dsv-vr.md, "Hypotheses").
func RegisterJSON() {}
