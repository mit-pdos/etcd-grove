//go:build rpcgen

// The dependency rpcgen's reflection dump needs (models/net/rpc/rpcgen.py: the module must import
// models.lab/rpcdesc); never built.
package craqnet

import _ "models.lab/rpcdesc"
