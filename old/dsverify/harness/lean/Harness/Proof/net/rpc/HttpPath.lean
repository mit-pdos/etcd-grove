/-
net/rpc's HTTP path `rpcPath` is well formed for the model of `net/http` (`http/Head.lean`'s
`wfPath`), so `ListenAndServe` and `serveConn` apply to an rpc address.
-/
module

public import Harness.Proof.net.rpc.Proto
public import Harness.Proof.net.http.Head

@[expose] public section

namespace Perennial

namespace net.rpc

theorem wfPath_rpcPath : net.http.wfPath rpcPath := by
  unfold net.http.wfPath rpcPath
  refine ⟨by simp, by decide, by decide⟩

end net.rpc

end Perennial
