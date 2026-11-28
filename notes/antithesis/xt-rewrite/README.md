# The `xt` frame change's mechanical rewrite (antithesis parity B1, option (b), 2026-11-26)

`raft.Step.spec`'s `%Hframe` gained the premise `(m.Type' = MsgAppResp → m.From' ≠ id → s.lt = W64 0)` and
`%Hxwframe` the widened premise, `xt := s'.gh.xt` in its ghost frame and the xw-growth conjunct; `StepEnd.gated`
takes `¬ XtRec id m s`. To replay on another branch, from `Proof/go_etcd_io/raft/v3`:

- `python3 frame_rw.py FILE...` on the files restating the frame or the bare ghost frame (TracedRaftStepBundle,
  TracedUntracedRaftStep, TracedRawNodeAdvance, RaftStepNoSnap, TracedNodeRun, RawNode__StepAbs, InvNodeRun,
  TracedRawNode, LemmasP3bXw);
- `python3 gated_rw.py FILE...` on `StepEnd`'s readers (appends `(by xtrec_tac)`);
- the one-argument appends to `%Hframe`'s users (the type's refutation, a traced node's `lt = 0`, an `Advance`
  step's own sender) and `(by xtx_tac) (by xta_tac)` on the `stepLeader` calls of `raft__Step/*`, by hand.

`changed-lines.txt` lists every changed `file:line` of the whole change (both commits), as built.
