/-
The proof of `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/selectWALFiles.lean`.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.selectWALFiles
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.walpb.Snapshot__GetIndex
public import LinuxFs.Spec.fmt.ErrorfErrs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Fs

/-- The names `readWALNames` returns from a directory `selectWALFiles` can read are segment names. -/
theorem walNamesOut_str {N : NameSet} {h : NamesH} {ws : List GoString} (hd : WalDirNamesOk N h)
    (ho : WalNamesOut N h ws) : ∀ n ∈ ws, ∃ s i, n = fmt.walNameStr s i := by
  intro n hn
  have hm := (ho.2.2.1 n hn).2
  obtain ⟨hN, hs⟩ := hd n hm.1
  exact hs (ho.2.2.2.1 n hN hn)

/-- `walSearchFrom` finds a position below its bound. -/
theorem walSearchFrom_lt {idxs : List w64} {index : w64} :
    ∀ {n k : Nat}, walSearchFrom idxs index n = some k → k < n
  | 0, _, h => by simp [walSearchFrom] at h
  | n + 1, k, h => by
    unfold walSearchFrom at h
    split at h
    · cases h; omega
    · exact Nat.lt_succ_of_lt (walSearchFrom_lt h)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [go_etcd_io.etcd.server.v3.storage.wal.walpb.Assumptions]

theorem argWf_uint64 (v : w64) :
    fmt.ArgWf (interface.mk go.uint64 #v) :=
  ⟨fun h => by simp [go.uint64, go.string] at h, fun _ => ⟨_, .uint64 v⟩,
    Or.inl (Or.inr (Or.inr (Or.inl (by simp [fmt.IsIntType]))))⟩

theorem argWf_int (v : w64) :
    fmt.ArgWf (interface.mk go.int #v) :=
  ⟨fun h => by simp [go.int, go.string] at h, fun _ => ⟨_, .int v⟩,
    Or.inl (Or.inr (Or.inr (Or.inl (by simp [fmt.IsIntType]))))⟩

theorem go_etcd_io.etcd.server.v3.storage.wal.selectWALFiles.wp_proof
    (HNames : go_etcd_io.etcd.server.v3.storage.wal.readWALNames.spec (GF := GF) (hG := hG))
    (HSearch : go_etcd_io.etcd.server.v3.storage.wal.searchIndex.spec (GF := GF) (hG := hG))
    (HSeq : go_etcd_io.etcd.server.v3.storage.wal.isValidSeq.spec (GF := GF) (hG := hG))
    (HIdx : go_etcd_io.etcd.server.v3.storage.wal.walpb.Snapshot.GetIndex.spec (GF := GF) (hG := hG))
    (HErrorf : fmt.ErrorfErrs.spec (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.server.v3.storage.wal.selectWALFiles.spec (GF := GF) (hG := hG) := by
  intro lg d sp s R j dq qc N dqn h hd
  wp_start as ⟨#Hlg, #Hos, #Hsi, Hp, Hperm, Hn, #Hsp⟩
  wp_auto
  wp_apply HNames lg d R j dq qc N dqn h $$ [Hp Hperm Hn] as %r %err ⟨Hp, Hperm, Hn, Hr⟩
  · iframe
    isplitl []
    · iexact Hlg
    isplitl []
    · iexact Hos
    iexact Hsi
  icases Hr with (⟨%ws, ⟨%herr, %hout⟩, Hws⟩ | ⟨%e, %herr, #He⟩)
  · subst herr
    try wp_auto
    wp_apply HIdx sp s $$ []
    · iexact Hsp
    try wp_auto
    have hstr := walNamesOut_str hd hout
    wp_apply HSearch lg r ws (DFrac.own 1) s.1 hstr $$ [Hws] as Hws
    · iframe
    try wp_auto
    cases hk : walSearch (ws.map walNameIdx) s.1 with
    | none =>
      simp only [Option.isSome_none]
      try wp_auto
      wp_apply HIdx sp s $$ []
      · iexact Hsp
      try wp_auto
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %asl ⟨Hasl, -⟩
      wp_apply HErrorf _ _ [interface.mkOk go.uint64 #s.1] [] (by
            intro ii hii
            left
            simp only [List.mem_cons, List.not_mem_nil, or_false, interface.mkOk] at hii
            cases hii
            exact argWf_uint64 _) $$ [Hasl] as %err2 #Herr2
      · iframe
        try simp only [BigSepL.bigSepL_nil]
        iempintro
      try wp_auto
      iapply HΦ
      iframe
      iright
      iexists err2
      isplitr
      · ipureintro; rfl
      iexact Herr2
    | some k =>
      simp only [Option.isSome_some]
      have hkl : k < ws.length := by
        have := walSearchFrom_lt hk; simpa using this
      ihave %Hrl := ownSlice_len _ _ _ $$ Hws
      ihave %Hwf := ownSlice_wf _ _ _ $$ Hws
      have hk0 : sint.nat (W64 (k : Int)) = k := by
        have : k < 2 ^ 63 := by
          have := Hrl.1; have : sint.nat r.len < 2 ^ 63 := by word
          omega
        word
      try wp_auto
      rw [if_pos (by refine ⟨by word, ?_, Hwf.2⟩; have := Hrl.1; word)]
      iclear Hlg
      icases (ownSlice_slice (W64 (k : Int)) r.len r (DFrac.own 1) ws
        ⟨by word, by have := Hrl.1; word, Int.le_refl _⟩).1 $$ Hws with ⟨Hw1, Hw2, Hw3⟩
      have hsub : subslice (sint.nat (W64 (k : Int))) (sint.nat r.len) ws = ws.drop k := by
        rw [hk0, subslice_def, ← Hrl.1, List.take_length]
      rw [hsub]
      have hstr' : ∀ n ∈ ws.drop k, ∃ s i, n = fmt.walNameStr s i :=
        fun n hn => hstr n (List.mem_of_mem_drop hn)
      wp_apply HSeq lg _ (ws.drop k) (DFrac.own 1) hstr' $$ [Hw2] as Hw2
      · iframe
      ihave Hws := (ownSlice_slice (W64 (k : Int)) r.len r (DFrac.own 1) ws
        ⟨by word, by have := Hrl.1; word, Int.le_refl _⟩).2 $$ [Hw1 Hw2 Hw3]
      · rw [hsub]; iframe
      cases hseq : walSeqOk 0 ((ws.drop k).map walNameSeq) with
      | false =>
        try wp_auto
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %asl ⟨Hasl, -⟩
        wp_apply HErrorf _ _ [interface.mkOk go.int #(W64 (k : Int))] [] (by
              intro ii hii
              left
              simp only [List.mem_cons, List.not_mem_nil, or_false, interface.mkOk] at hii
              cases hii
              exact argWf_int _) $$ [Hasl] as %err2 #Herr2
        · iframe
          try simp only [BigSepL.bigSepL_nil]
          iempintro
        try wp_auto
        iapply HΦ
        iframe
        iright
        iexists err2
        isplitr
        · ipureintro; rfl
        iexact Herr2
      | true =>
        try wp_auto
        iapply HΦ
        iframe
        ileft
        iexists ws
        iframe
        ipureintro
        refine ⟨rfl, by word, hout, ?_, ?_⟩
        · rw [hk0]; exact hk
        · rw [hk0]; exact hseq
  · subst herr
    try wp_auto
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %asl ⟨Hasl, -⟩
    wp_apply HErrorf _ _ [GoInterface.ok e] [e] (by
          intro ii hii
          right
          simpa using hii) $$ [Hasl] as %err2 #Herr2
    · iframe
      iapply (BigSepL.bigSepL_singleton (Φ := fun _ e => errOk (GF := GF) e)).2
      iexact He
    try wp_auto
    iapply HΦ
    iframe
    iright
    iexists err2
    isplitr
    · ipureintro; rfl
    iexact Herr2

end proof

end EtcdGrove
end Perennial
