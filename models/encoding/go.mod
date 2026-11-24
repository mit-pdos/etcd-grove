// The model of the standard library's encoding/json: the package's Go source as the model
// changes it, built only in place of the real package (models/goroot.py: a `go build -overlay`
// file, or a GOROOT of links for goose). This module is never built; it keeps these files out of
// models.lab's `./...` (as models/net/go.mod does for net/rpc and net/http).
module models.lab/stdmodels/encoding

go 1.27
