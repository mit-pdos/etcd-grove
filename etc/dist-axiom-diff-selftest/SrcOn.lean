/- `etc/dist-axiom-diff.py --selftest`'s auth-on in-process source: a proved `theorem` (no spec of its own),
as `client.client_put_on` (not built: read as text only). Its reply gives no revision bound. -/
theorem st_on (api : Loc) (k : GoString) (hk : k ≠ []) :
    {{ threadTok ∗ isGrpcRpcMd addr (putSpecOn E) ∗ clientOpAuOn E (.put k) Q }}
      (App (Val (api @!! go!"Put")) (Val #k))
    {{ (m : PutRespM), RET #m; threadTok ∗ putReplied E k Q m ∗ writeGrantOn E k }} := by
  exact st_on_proved_elsewhere
