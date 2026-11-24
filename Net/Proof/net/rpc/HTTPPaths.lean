/-
`DefaultRPCPath` and `DefaultDebugPath` are literal patterns of the mux (`net.http.litPattern`):
the premises `Server.HandleHTTP.spec` takes of its paths, for `HandleHTTP` and its callers.
-/
module

public import Net.Proof.net.http.MuxDefs
public import Net.Spec.net.rpc.HandleHTTP

@[expose] public section

noncomputable section

namespace Perennial

namespace net.rpc

theorem litPattern_rpc : net.http.litPattern defaultRPCPath := by
  unfold net.http.litPattern defaultRPCPath; decide

theorem litPattern_debug : net.http.litPattern defaultDebugPath := by
  unfold net.http.litPattern defaultDebugPath; decide

end net.rpc
end Perennial
