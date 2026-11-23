//go:build tools

package swiftnet

// rpcgen (models/net/rpc/rpcgen.py) derives the codec's input by reflection through
// models.lab/rpcdesc, run from this module: the import keeps it required (go mod tidy).
import _ "models.lab/rpcdesc"
