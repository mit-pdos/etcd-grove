"""(option (b)) the mechanical rewrite of raft.Step.spec's restated frames:
(1) %Hframe gains the append-response premise; (2) %Hxwframe's premise widens, its gh frame gains xt,
and it gains the xw-growth conjunct; (3) the bare gh-frame `{ s.gh with xw := s'.gh.xw, xs := s'.gh.xs }`
gains `xt := s'.gh.xt`."""
import re, sys
for p in sys.argv[1:]:
    s = open(p).read(); o = s
    # (1) Hframe premise
    s = re.sub(r"\(m\.Type' = MsgStorageAppendResp → sn = none\) → NetFrame s s'(⌝|\))",
               lambda mm: "(m.Type' = MsgStorageAppendResp → sn = none) →\n" + " "*19 +
               "(m.Type' = MsgAppResp → m.From' ≠ id → s.lt = W64 0) → NetFrame s s'" + mm.group(1), s)
    # (2) Hxwframe premise + conjunct
    s = re.sub(r"m\.Type' = MsgTransferLeader → NetFrame s \{ s' with gh := s\.gh \} ∧(\s*)s'\.gh = \{ s\.gh with xw := s'\.gh\.xw, xs := s'\.gh\.xs \} ∧ ∀ p, p ∈ s\.gh\.xw → p ∈ s'\.gh\.xw",
               lambda mm: ("(m.Type' = MsgTransferLeader ∨ (m.Type' = MsgAppResp ∧ m.From' ≠ id ∧ s.lt ≠ W64 0)) →"
                           " NetFrame s { s' with gh := s.gh } ∧" + mm.group(1) +
                           "s'.gh = { s.gh with xw := s'.gh.xw, xt := s'.gh.xt, xs := s'.gh.xs } ∧"
                           " (∀ p, p ∈ s.gh.xw → p ∈ s'.gh.xw) ∧" + mm.group(1) +
                           "(∀ p, p ∈ s'.gh.xw → p ∈ s.gh.xw ∨ (p = (s.lead, s.term) ∧ s.role = .follower ∧ s.lead ≠ W64 0))"), s)
    # (3) bare gh-frame
    s = s.replace("{ s.gh with xw := s'.gh.xw, xs := s'.gh.xs }", "{ s.gh with xw := s'.gh.xw, xt := s'.gh.xt, xs := s'.gh.xs }")
    if s != o:
        open(p, 'w').write(s); print("rewrote", p)
