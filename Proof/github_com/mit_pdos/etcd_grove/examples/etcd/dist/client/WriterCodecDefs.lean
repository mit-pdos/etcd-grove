/- Lean-first (no Rocq counterpart).

# The writers' codec's bytes, read back (#50 N10a, `writerCodec.wp_proof`)

`kvsBytes`/`recsBytes` (`WriterWire.lean`) are the count, then the elements' bytes (`kvsBody`, `recsBody`);
the decoders read the elements one at a time, so their loops' invariant is the bytes so far `encU64 n ++
kvsBody ps ++ r` (`kvsBody_snoc`, `recsBody_snoc`). The elements' bytes determine the elements (`kvsBody_inj`,
`recsBody_inj`: the encodings' injectivity, `enc`'s `encU64_append_inj`, `encStr_append_inj`), so a decoding
that read the wire's bytes of `ps0` and nothing else returned `ps0` (`kvsBytes_dec`, `recsBytes_dec`; a
too-long `ps0` has no bytes on the wire, `capped`, and nothing decodes from none).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.WriterWire

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open etcd_dist etcdstart
open github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc

section pure
variable [GooseExts]

theorem encStr_length (s : GoString) : (encStr s).length = 8 + s.length := by
  simp [encStr, encU64_length]

/-- `kvsBytes`'s elements: each Put's key and value. -/
def kvsBody (ps : List wkv) : List w8 := ps.flatMap (fun p => encStr p.Key' ++ encStr p.Val')

/-- `recsBytes`'s elements: each record's revision, key and value. -/
def recsBody (rs : List wrec) : List w8 :=
  rs.flatMap (fun r => encU64 r.Rev' ++ encStr r.Key' ++ encStr r.Val')

theorem kvsBytes_eq (ps : List wkv) : kvsBytes ps = encU64 (W64 ps.length) ++ kvsBody ps := rfl

theorem recsBytes_eq (rs : List wrec) : recsBytes rs = encU64 (W64 rs.length) ++ recsBody rs := rfl

theorem kvsBody_nil : kvsBody [] = [] := rfl

theorem recsBody_nil : recsBody [] = [] := rfl

theorem kvsBody_cons (p : wkv) (ps : List wkv) :
    kvsBody (p :: ps) = encStr p.Key' ++ (encStr p.Val' ++ kvsBody ps) := by
  simp [kvsBody]

theorem recsBody_cons (r : wrec) (rs : List wrec) :
    recsBody (r :: rs) = encU64 r.Rev' ++ (encStr r.Key' ++ (encStr r.Val' ++ recsBody rs)) := by
  simp [recsBody]

theorem kvsBody_snoc (ps : List wkv) (p : wkv) :
    kvsBody (ps ++ [p]) = kvsBody ps ++ (encStr p.Key' ++ encStr p.Val') := by
  simp [kvsBody]

theorem recsBody_snoc (rs : List wrec) (r : wrec) :
    recsBody (rs ++ [r]) = recsBody rs ++ (encU64 r.Rev' ++ encStr r.Key' ++ encStr r.Val') := by
  simp [recsBody]

theorem kvsBody_take_succ (ps : List wkv) (j : Nat) (p : wkv) (h : ps[j]? = some p) :
    kvsBody (ps.take (j + 1)) = kvsBody (ps.take j) ++ (encStr p.Key' ++ encStr p.Val') := by
  rw [List.take_add_one, h]
  exact kvsBody_snoc _ _

theorem recsBody_take_succ (rs : List wrec) (j : Nat) (r : wrec) (h : rs[j]? = some r) :
    recsBody (rs.take (j + 1)) =
      recsBody (rs.take j) ++ (encU64 r.Rev' ++ encStr r.Key' ++ encStr r.Val') := by
  rw [List.take_add_one, h]
  exact recsBody_snoc _ _

/-- **The Puts' bytes determine the Puts.** -/
theorem kvsBody_inj : ∀ (ps qs : List wkv), kvsBody ps = kvsBody qs →
    (kvsBody ps).length < 2 ^ 64 → ps = qs
  | [], [], _, _ => rfl
  | [], q :: qs, h, _ => by
    exfalso
    have := congrArg List.length h
    rw [kvsBody_cons, kvsBody_nil] at this
    simp only [List.length_nil, List.length_append, encStr_length] at this
    omega
  | p :: ps, [], h, _ => by
    exfalso
    have := congrArg List.length h
    rw [kvsBody_cons, kvsBody_nil] at this
    simp only [List.length_nil, List.length_append, encStr_length] at this
    omega
  | p :: ps, q :: qs, h, hl => by
    have hl' := hl
    rw [h] at hl'
    simp only [kvsBody_cons] at h hl hl'
    simp only [List.length_append, encStr_length] at hl hl'
    obtain ⟨hk, h⟩ := encStr_append_inj h (by omega) (by omega)
    obtain ⟨hv, h⟩ := encStr_append_inj h (by omega) (by omega)
    have ih := kvsBody_inj ps qs h (by omega)
    cases p; cases q
    simp only at hk hv
    subst hk hv ih
    rfl

/-- **The records' bytes determine the records.** -/
theorem recsBody_inj : ∀ (rs qs : List wrec), recsBody rs = recsBody qs →
    (recsBody rs).length < 2 ^ 64 → rs = qs
  | [], [], _, _ => rfl
  | [], q :: qs, h, _ => by
    exfalso
    have := congrArg List.length h
    rw [recsBody_cons, recsBody_nil] at this
    simp only [List.length_nil, List.length_append, encStr_length, encU64_length] at this
    omega
  | r :: rs, [], h, _ => by
    exfalso
    have := congrArg List.length h
    rw [recsBody_cons, recsBody_nil] at this
    simp only [List.length_nil, List.length_append, encStr_length, encU64_length] at this
    omega
  | r :: rs, q :: qs, h, hl => by
    have hl' := hl
    rw [h] at hl'
    simp only [recsBody_cons] at h hl hl'
    simp only [List.length_append, encStr_length, encU64_length] at hl hl'
    obtain ⟨hr, h⟩ := encU64_append_inj h
    obtain ⟨hk, h⟩ := encStr_append_inj h (by omega) (by omega)
    obtain ⟨hv, h⟩ := encStr_append_inj h (by omega) (by omega)
    have ih := recsBody_inj rs qs h (by omega)
    cases r; cases q
    simp only at hr hk hv
    subst hr hk hv ih
    rfl

/-- **A decoding of the Puts' wire bytes**: bytes read as a count and then the Puts `ps`, and
nothing else, were the wire's bytes of `ps0` only if `ps` is `ps0` (whose bytes fit). -/
theorem kvsBytes_dec {ps0 ps : List wkv} {n : w64}
    (h : capped (kvsBytes ps0) = encU64 n ++ kvsBody ps ++ []) :
    ps = ps0 ∧ (kvsBytes ps0).length < 2 ^ 63 := by
  rw [List.append_nil] at h
  by_cases hl : (kvsBytes ps0).length < 2 ^ 63
  · rw [capped_of _ hl, kvsBytes_eq] at h
    obtain ⟨-, h⟩ := encU64_append_inj h
    refine ⟨(kvsBody_inj ps0 ps h ?_).symm, hl⟩
    rw [kvsBytes_eq] at hl
    simp only [List.length_append] at hl
    omega
  · exfalso
    simp only [capped, hl, ↓reduceIte] at h
    have := congrArg List.length h
    simp only [List.length_nil, List.length_append, encU64_length] at this
    omega

/-- **A decoding of the log's wire bytes** (`kvsBytes_dec`'s for the records). -/
theorem recsBytes_dec {rs0 rs : List wrec} {n : w64}
    (h : capped (recsBytes rs0) = encU64 n ++ recsBody rs ++ []) :
    rs = rs0 ∧ (recsBytes rs0).length < 2 ^ 63 := by
  rw [List.append_nil] at h
  by_cases hl : (recsBytes rs0).length < 2 ^ 63
  · rw [capped_of _ hl, recsBytes_eq] at h
    obtain ⟨-, h⟩ := encU64_append_inj h
    refine ⟨(recsBody_inj rs0 rs h ?_).symm, hl⟩
    rw [recsBytes_eq] at hl
    simp only [List.length_append] at hl
    omega
  · exfalso
    simp only [capped, hl, ↓reduceIte] at h
    have := congrArg List.length h
    simp only [List.length_nil, List.length_append, encU64_length] at this
    omega

end pure

end etcd_dist_client
end EtcdGrove
end Perennial
