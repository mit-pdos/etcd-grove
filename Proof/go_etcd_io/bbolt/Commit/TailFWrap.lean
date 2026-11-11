/-
**`Commit`'s tail lemmas over the flagged writer side** (U10n): `Commit/TailFPure`'s `noFl` device
applied to the tail's lemmas stated over `wdbOK` (`cm_write_pre`, `cm_write_part`, `cm_pub_ok`,
`wdbOK_written`, `cm_unpub_ok`, `cmPubPre_noSync`): each is stated here over `wdbOK' fr` (and, where
the result is the writer side after a write, gives `wdbOK' fr` back, by `flExtPend`: the slots a
write changes are `W` slots, not pending).
-/
module

public import Proof.go_etcd_io.bbolt.Commit.TailFPure
public import Proof.go_etcd_io.bbolt.Commit.PubOk
public import Proof.go_etcd_io.bbolt.Commit.PubPre
public import Proof.go_etcd_io.bbolt.Commit.TailAcc

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [GooseExts]

theorem cm_write_pre' (fr : Bool) (D : Data) (X : WX) (w : WDb) (b : Loc) (l : Nat)
    (hpre : cmPubPre D X w) (hok : wdbOK' fr w) (hms : w.ms = some (b, l))
    (hmapl : X.t.mv.pgid'.toNat * 4096 ≤ l) :
    bufsOK X.t.bufs (l / 4096) ∧ (∀ s ∈ bufSlots X.t.bufs, s ∈ w.W) ∧
      (∀ s, s < l / 4096 → w.m.size < 4096 * (s + 1) → s ∈ w.W) ∧
      (∀ s ∈ w.W, 4096 * (s + 1) ≤ w.m.size → (w.wb s).length = 4096) ∧
      (∀ s ∈ w.W, l / 4096 ≤ s → 4096 * (s + 1) ≤ w.m.size) :=
  cm_write_pre D X w.noFl b l (cmPubPre_noFl D X w hpre) (wdbOK'_noFl fr w hok) hms hmapl

theorem cm_write_part' (fr : Bool) (w : WDb) (m' : OsMeta) (S : List Nat) (wb' wbF : Nat → List w8)
    (hok : wdbOK' fr w)
    (hw : ∀ s ∈ S, 4096 * s < m'.size → m'.size < 4096 * (s + 1) →
      m'.size - 4096 * s ≤ (wb' s).length)
    (hgrow : m'.size = w.m.size ∨ m'.size % 4096 = 0)
    (hF : ∀ s, (s ∈ S ∧ wbF s = wb' s) ∨ wbF s = w.wb s) :
    ∀ s, 4096 * s < m'.size → m'.size < 4096 * (s + 1) → m'.size - 4096 * s ≤ (wbF s).length :=
  cm_write_part w.noFl m' S wb' wbF (wdbOK'_noFl fr w hok) hw hgrow hF

theorem cm_pub_ok' (fr : Bool) (D : Data) (X : WX) (w : WDb) (b : Loc) (l : Nat) (Pg : Pages)
    (m' m'' : OsMeta) (wb' : Nat → List w8) (hpre : cmPubPre D X w) (hpg : cmPubPg D X w Pg)
    (htx : X.t.mv.txid' = w.wtxid) (hok : wdbOK' fr w) (hms : w.ms = some (b, l))
    (hmapl : X.t.mv.pgid'.toNat * 4096 ≤ l)
    (hm' : w.m.size ≤ m'.size ∧ m'.size ≤ max w.m.size l ∧ m'.maps = w.m.maps ∧
      ∀ s ∈ bufSlots X.t.bufs ++ cmTail w (bufSlots X.t.bufs) l, 4096 * (s + 1) ≤ m'.size →
        (wb' s).length = 4096)
    (hm'' : m''.size = m'.size ∧ m''.maps = m'.maps) (hsz63 : m'.size < 2 ^ 63)
    (hin : ∀ s ∈ bufSlots X.t.bufs, 4096 * (s + 1) ≤ m'.size)
    (hch : ∀ id pg, X.t.bufs !! id = some pg → ∀ j < 1 + pageOverflow pg,
      wb' (id.toNat + j) = pageChunk pg j)
    (hpart : ∀ s, 4096 * s < m'.size → m'.size < 4096 * (s + 1) →
      m'.size - 4096 * s ≤ (wbUpd (cmTail w (bufSlots X.t.bufs) l) wb' w.wb s).length) :
    cpOK w.C w.fl b l X.t.mv Pg D ((bufSlots X.t.bufs).filter (pubP w X Pg)) wb' ∧
    wdbOK ((w.reslot m'' ((bufSlots X.t.bufs).filter (fun s => !pubP w X Pg s) ++
        (cmTail w (bufSlots X.t.bufs) l ++
          wMinus w.W (bufSlots X.t.bufs ++ cmTail w (bufSlots X.t.bufs) l)))
      (wbUpd ((bufSlots X.t.bufs).filter (fun s => !pubP w X Pg s)) wb'
        (wbUpd (cmTail w (bufSlots X.t.bufs) l) wb' w.wb))).withC (pubC w.C X.t.mv Pg)) := by
  have h := cm_pub_ok D X w.noFl b l Pg m' m'' wb' (cmPubPre_noFl D X w hpre)
    (cmPubPg_noFl D X w Pg hpg) htx (wdbOK'_noFl fr w hok) hms hmapl rfl hm' hm'' hsz63 hin hch hpart
  exact ⟨cpOK_noFl w b l X.t.mv Pg D _ wb' h.1, h.2⟩

/-- A write of `W` slots leaves the pending slots' bytes, through `wbUpd3`'s three layers. -/
theorem wbUpd3_pend (fr : Bool) (w : WDb) (h : wdbOK' fr w) (SB T : List Nat) (P : Nat → Bool)
    (wb' : Nat → List w8) (hS : ∀ s ∈ SB ++ T, s ∈ w.W) : ∀ s, s ∈ pendSlots w.fl →
      wbUpd (SB.filter P) wb' (wbUpd (SB.filter (fun s => !P s)) wb' (wbUpd T wb' w.wb)) s =
        w.wb s := by
  intro s hs
  rcases wbUpd3_cases SB T P wb' w.wb s with ⟨hm, -⟩ | e
  · exact absurd hs (wdbOK'_W_not_pend fr w h s (hS s hm))
  · exact e

/-- **`wdbOK_written` over the flagged writer side.** -/
theorem wdbOK_written' (fr : Bool) (w : WDb) (m : OsMeta) (SBT : List Nat) (wb' : Nat → List w8)
    (hok : wdbOK' fr w) (hep : flExtPend w) (hsub : ∀ s ∈ SBT, s ∈ w.W) (hsz1 : w.m.size ≤ m.size)
    (hsz2 : m.size ≤ max w.m.size (mapLen w.ms)) (hsz63 : m.size < 2 ^ 63)
    (hmaps : m.maps = w.m.maps)
    (hlen : ∀ s ∈ SBT, 4096 * (s + 1) ≤ m.size → (wb' s).length = 4096)
    (hold : ∀ s ∈ w.W, s ∉ SBT → 4096 * (s + 1) ≤ w.m.size)
    (hpart : ∀ s, 4096 * s < m.size → m.size < 4096 * (s + 1) →
      m.size - 4096 * s ≤ (wbUpd SBT wb' w.wb s).length) :
    wdbOK' fr (w.reslot m (SBT ++ wMinus w.W SBT) (wbUpd SBT wb' w.wb)) := by
  have h := wdbOK_written w.noFl m SBT wb' (wdbOK'_noFl fr w hok) hsub hsz1 hsz2 hsz63 hmaps hlen
    hold rfl hpart
  exact wdbOK'_of_noFl_wb fr w _ rfl rfl hep (wbUpd_pend fr w hok SBT wb' hsub)
    (wdbOK'_flClause fr w hok) h

/-- **`cm_unpub_ok` over the flagged writer side.** -/
theorem cm_unpub_ok' (fr : Bool) (w : WDb) (m : OsMeta) (SB T : List Nat) (P : Nat → Bool)
    (wb' : Nat → List w8) (hok : wdbOK' fr w) (hep : flExtPend w) (hsub : ∀ s ∈ SB ++ T, s ∈ w.W)
    (hsz1 : w.m.size ≤ m.size) (hsz2 : m.size ≤ max w.m.size (mapLen w.ms))
    (hsz63 : m.size < 2 ^ 63) (hmaps : m.maps = w.m.maps)
    (hlen : ∀ s ∈ SB ++ T, 4096 * (s + 1) ≤ m.size → (wb' s).length = 4096)
    (hold : ∀ s ∈ w.W, s ∉ SB ++ T → 4096 * (s + 1) ≤ w.m.size)
    (hpart : ∀ s, 4096 * s < m.size → m.size < 4096 * (s + 1) →
      m.size - 4096 * s ≤ (wbUpd (SB.filter P) wb' (wbUpd (SB.filter (fun s => !P s)) wb'
        (wbUpd T wb' w.wb)) s).length) :
    wdbOK' fr (w.reslot m (SB.filter P ++ (SB.filter (fun s => !P s) ++ (T ++ wMinus w.W (SB ++ T))))
      (wbUpd (SB.filter P) wb' (wbUpd (SB.filter (fun s => !P s)) wb' (wbUpd T wb' w.wb)))) := by
  have h := cm_unpub_ok w.noFl m SB T P wb' (wdbOK'_noFl fr w hok) hsub hsz1 hsz2 hsz63 hmaps hlen
    hold rfl hpart
  exact wdbOK'_of_noFl_wb fr w _ rfl rfl hep (wbUpd3_pend fr w hok SB T P wb' hsub)
    (wdbOK'_flClause fr w hok) h

/-- **`cmPubPre_noSync` over the flagged writer side.** -/
theorem cmPubPre_noSync' (fr : Bool) (D : Data) (X1 X2 Xt : WX) (w2 : WDb) (fl1 : FLPg)
    (txid : w64)
    (hsp : spillOK X1 X2 w2.C fl1 w2.fl txid) (hD : D = wtxData X1)
    (hbufs : spillBufs X2 w2.C w2.fl)
    (hpm : Xt.t.pm = X2.t.pm) (hbf : Xt.t.bufs = X2.t.bufs) (hpg : Xt.t.mv.pgid' = X2.t.mv.pgid')
    (hroot : Xt.t.mv.root'.root'.toNat = X2.rootPage) (htxid : Xt.t.mv.txid' = X2.t.mv.txid')
    (htxC : Xt.t.mv.txid'.toNat = w2.C.txid + 1)
    (hfl : Xt.t.mv.freelist'.toNat = pgidNoFreelist)
    (hmg : Xt.t.mv.magic'.toNat = boltMagic) (hvr : Xt.t.mv.version'.toNat = boltVersion)
    (hps : Xt.t.mv.pageSize'.toNat = 4096) (hCh : w2.C.hwm ≤ X2.t.mv.pgid'.toNat)
    (hml : Xt.t.mv.pgid'.toNat * 4096 ≤ 0xFFFFFFFFFFFF) (htC : treeOK w2.C) (hok : wdbOK' fr w2)
    (hfb : flBelow w2.fl w2.C (some (w2.C.txid + 1))) (htx2 : w2.C.txid + 2 < 2 ^ 64)
    (hnp : ∀ s ∈ treeSlots (spillC X2 w2.C.pages), s ∉ pendSlots w2.fl)
    (hmc : markCov X2 w2.C.hwm) :
    cmPubPre D Xt w2 :=
  cmPubPre_noSync D X1 X2 Xt w2.noFl fl1 txid hsp hD hbufs hpm hbf hpg hroot htxid htxC hfl hmg
    hvr hps hCh hml htC (wdbOK'_noFl fr w2 hok) hfb htx2 hnp hmc

end pure

end bbolt
end EtcdGrove
end Perennial
