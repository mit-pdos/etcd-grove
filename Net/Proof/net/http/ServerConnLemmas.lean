/-
The connection's helpers (`ServerConn.lean`): `Server.trackConn` and `conn.setState` (with no
`ConnState` hook), for the proofs of the server's methods.
-/
module

public import Net.Proof.net.http.ServerConn
public import Perennial.Proof.sync.Link
public import Perennial.Proof.sync.atomic.Link
public import Perennial.Proof.time.Link
public import Spec.bufio.Writer__Reset

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace net.http

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem' : net.http.Assumptions]
variable [π : NetProtoGS]

/-- `s.trackConn(c, add)`. -/
theorem wp_trackConn (s c : Loc) (add : Bool) :
    {{ srvConst (GF := GF) s }}
      (App (App (Val (s @!! go.GoType.PointerType net.http.Server.ty @!! go!"trackConn")) (Val #c))
        (Val #add))
    {{ RET #(); True }} := by
  wp_start as #Hs
  iunfold srvConst at Hs
  icases Hs with ⟨#Htime, #Hsync, #Hatomic, #Hmu, #Hcs⟩
  wp_apply wp_with_defer as %defer defer
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hown, Hinv⟩
  iunfold srvMuInv at Hinv
  icases Hinv with ⟨Hac, Hls⟩
  iunfold mapField at Hac
  icases Hac with ⟨%m, Hm, Hmm⟩
  wp_auto
  icases Hmm with (%Hnil | ⟨%g, Hg⟩)
  · subst Hnil
    simp only [decide_true]
    wp_apply (wp_map_make1 (K := Loc) (V := Unit) _ _) as %m' Hg
    cases add
    · wp_auto
      wp_apply (wp_mapDelete (K := Loc) (V := Unit) _ _ c _ _) $$ [$Hg] as Hg
      wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hown Hm Hg Hls]
      · inext; iunfold srvMuInv; iframe Hls; iunfold mapField; iexists _; iframe Hm; iright; iexists _; iexact Hg
      iapply HΦ; itrivial
    · wp_auto
      wp_apply (wp_mapInsert (K := Loc) (V := Unit) _ _ _ c ()) $$ [$Hg] as Hg
      wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hown Hm Hg Hls]
      · inext; iunfold srvMuInv; iframe Hls; iunfold mapField; iexists _; iframe Hm; iright; iexists _; iexact Hg
      iapply HΦ; itrivial
  · ihave %Hnn := ownMap_not_nil _ _ _ $$ Hg
    simp only [Hnn, decide_false]
    wp_auto
    cases add
    · wp_auto
      wp_apply (wp_mapDelete (K := Loc) (V := Unit) _ _ c _ _) $$ [$Hg] as Hg
      wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hown Hm Hg Hls]
      · inext; iunfold srvMuInv; iframe Hls; iunfold mapField; iexists _; iframe Hm; iright; iexists _; iexact Hg
      iapply HΦ; itrivial
    · wp_auto
      wp_apply (wp_mapInsert (K := Loc) (V := Unit) _ _ _ c ()) $$ [$Hg] as Hg
      wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hown Hm Hg Hls]
      · inext; iunfold srvMuInv; iframe Hls; iunfold mapField; iexists _; iframe Hm; iright; iexists _; iexact Hg
      iapply HΦ; itrivial


/-- `c.setState(nc, st, runHooks)`, with no `ConnState` hook: the connection tracked or
untracked, its packed state stored. -/
theorem wp_setState (c s : Loc) (nc : GoInterface) (st : w64)
    (hst : 0 ≤ sint.Z st ∧ sint.Z st ≤ 255) :
    {{ structFieldRef net.http.conn go!"server" c ↦□ s ∗ srvConst (GF := GF) s ∗
        (∃ v : w64, sync.atomic.ownUint64 (structFieldRef net.http.conn go!"curState" c)
          (DFrac.own 1) v) }}
      (App (App (App (Val (c @!! go.GoType.PointerType net.http.conn.ty @!! go!"setState"))
        (Val #nc)) (Val #st)) (Val #true))
    {{ RET #(); ∃ v : w64, sync.atomic.ownUint64 (structFieldRef net.http.conn go!"curState" c)
          (DFrac.own 1) v }} := by
  wp_start as ⟨#Hsrv, #Hs, %v, Hst⟩
  have h1 : ¬ (sint.Z (W64 255) < sint.Z st) := by
    have : sint.Z (W64 255) = 255 := by decide
    omega
  have h2 : ¬ (sint.Z st < sint.Z (W64 0)) := by
    have : sint.Z (W64 0) = 0 := by decide
    omega
  ihave #Hs' := Hs
  iunfold srvConst at Hs'
  icases Hs' with ⟨#Htime, #Hsync, #Hatomic, #Hmu, #Hcs⟩
  wp_auto
  all_goals repeat (first | wp_if_destruct | (wp_apply wp_trackConn $$ [$Hs]) |
    (wp_apply time.wp_Now as %tn -) | (wp_apply time.Time.wp_Unix as %x -) | wp_auto)
  all_goals try (by_cases h4 : st = W64 4 <;> simp only [h4, decide_true, decide_false])
  all_goals repeat (first | wp_if_destruct | (wp_apply wp_trackConn $$ [$Hs]) |
    (wp_apply time.wp_Now as %tn -) | (wp_apply time.Time.wp_Unix as %x -) | wp_auto)
  all_goals try simp only [h1, decide_false]
  all_goals repeat (first | wp_if_destruct | (wp_apply wp_trackConn $$ [$Hs]) |
    (wp_apply time.wp_Now as %tn' -) | (wp_apply time.Time.wp_Unix as %x' -) | wp_auto)
  all_goals try (exfalso; omega)
  all_goals try (wp_apply time.wp_Now as %tn'' -)
  all_goals try (wp_apply time.Time.wp_Unix as %x'' -)
  all_goals try wp_auto
  all_goals try (
    wp_bind (App (Val #(methods _ _ _)) _)
    iapply (sync.atomic.Uint64.wp_Store (structFieldRef net.http.conn go!"curState" c) _)
    · iPkgInit
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    inext
    iexists v
    iframe Hst
    iintro Hst
    imod Hmask
    imodintro
    wp_auto
    iapply HΦ; iexists _; iexact Hst)
  all_goals sorry

/-- `bw.Available()` of a writer holding nothing: its buffer's size. -/
theorem wp_rawAvailable [bufio.Assumptions] (bw : Loc) (sz : Nat) :
    {{ EtcdGrove.bufio.rawWriter (GF := GF) bw sz }}
      (App (Val (bw @!! go.GoType.PointerType bufio.Writer.ty @!! go!"Available")) (Val #()))
    {{ (n : w64), RET #n; ⌜sint.Z n = sz⌝ ∗ EtcdGrove.bufio.rawWriter bw sz }} := by
  wp_start as Hraw
  iunfold EtcdGrove.bufio.rawWriter at Hraw
  icases Hraw with ⟨%v, %bs, Hb, Hbuf, %Hv⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hbuf
  wp_auto
  iapply HΦ
  isplitr
  · ipureintro
    obtain ⟨h1, h2, h3⟩ := Hv
    rw [h3]
    have : (sint.Z v.buf'.len : Int) = sz := by
      rw [← h1, Hlen.1]; exact (Int.toNat_of_nonneg Hlen.2).symm
    word
  iunfold EtcdGrove.bufio.rawWriter
  iexists v, bs
  iframe Hb Hbuf
  ipureintro; exact Hv

/-- `bufioWriterPool(size)` of 2048 and 4096. -/
theorem wp_bufioWriterPool (n : w64) :
    {{ (True : IProp GF) }}
      (App (Val (@! net.http.bufioWriterPool)) (Val #n))
    {{ (p : Loc), RET #p; ⌜(n = W64 2048 → p = globalAddr net.http.bufioWriter2kPool) ∧
        (n = W64 4096 → p = globalAddr net.http.bufioWriter4kPool)⌝ }} := by
  wp_start
  wp_auto
  by_cases h2 : n = W64 2048 <;> by_cases h4 : n = W64 4096 <;>
    simp only [h2, h4, decide_true, decide_false] <;> wp_auto
  all_goals try (simp only [h2, h4, decide_true, decide_false]; wp_auto)
  all_goals (iapply HΦ; ipureintro; constructor <;> intro h <;> simp_all)

/-- `putBufioWriter(bw)` of a writer holding nothing with a buffer of 2048 or 4096 bytes: reset and
put back in its pool. -/
theorem wp_putBufioWriter [bufio.Assumptions]
    (wp_Reset : EtcdGrove.bufio.Writer.Reset.spec (GF := GF) (hG := hG)) (bw : Loc) (sz : Nat)
    (hsz : sz = 2048 ∨ sz = 4096) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ wPools ∗ EtcdGrove.bufio.rawWriter (GF := GF) bw sz }}
      (App (Val (@! net.http.putBufioWriter)) (Val #bw))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hpools, Hraw⟩
  wp_auto
  wp_apply wp_Reset bw sz _ $$ [$Hraw] as Hraw
  · ipureintro; left; rfl
  wp_apply wp_rawAvailable bw sz $$ [$Hraw] as %n ⟨%Hn, Hraw⟩
  wp_apply wp_bufioWriterPool n as %p %Hp
  iunfold wPools at Hpools
  icases Hpools with ⟨#H2, #H4⟩
  wp_if_destruct
  · iapply HΦ; itrivial
  · rcases hsz with rfl | rfl
    · have : n = W64 2048 := by word
      rw [Hp.1 this]
      wp_apply sync.Pool.wp_Put $$ [$H2 Hraw]
      · iunfold wPoolP; iexists bw; iframe Hraw; ipureintro; rfl
      iapply HΦ; itrivial
    · have : n = W64 4096 := by word
      rw [Hp.2 this]
      wp_apply sync.Pool.wp_Put $$ [$H4 Hraw]
      · iunfold wPoolP; iexists bw; iframe Hraw; ipureintro; rfl
      iapply HΦ; itrivial

end lemmas

end net.http
end Perennial
