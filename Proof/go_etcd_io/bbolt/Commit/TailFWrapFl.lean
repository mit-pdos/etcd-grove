/-
**`cmPubPre_commitFl` over the flagged writer side** (U10n): `Commit/PubFl`'s lemma through
`Commit/TailFPure`'s `noFl` device (`cmPubPre` and the spill's facts do not read the synced
freelist page).
-/
module

public import Proof.go_etcd_io.bbolt.Commit.TailFPure
public import Proof.go_etcd_io.bbolt.Commit.PubFl

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [GooseExts]

theorem cmPubPre_commitFl' (fr : Bool) (D : Data) (X1 X2 X3 X4 : WX) (w2 w4 : WDb) (fl1 : FLPg)
    (txid0 : w64) (p4 : Loc) (id4 : w64)
    (hsp : spillOK X1 X2 w2.C fl1 w2.fl txid0) (hD : D = wtxData X1)
    (hbufs : spillBufs X2 w2.C w2.fl)
    (hX3pm : X3.t.pm = X2.t.pm) (hX3bf : X3.t.bufs = X2.t.bufs)
    (hX3pg : X3.t.mv.pgid' = X2.t.mv.pgid')
    (hroot3 : X3.t.mv.root'.root'.toNat = X2.rootPage) (htxid3 : X3.t.mv.txid' = X2.t.mv.txid')
    (hmg : X3.t.mv.magic'.toNat = boltMagic) (hvr : X3.t.mv.version'.toNat = boltVersion)
    (hps : X3.t.mv.pageSize'.toNat = 4096)
    (hal : allocRes X3 X4 w2.fl w4.fl w2.wtxid (flCount w2.fl) p4 id4) (hC4 : w4.C = w2.C)
    (htxC : X3.t.mv.txid'.toNat = w2.C.txid + 1)
    (hCh : w2.C.hwm ≤ X2.t.mv.pgid'.toNat)
    (hml : X4.t.mv.pgid'.toNat * 4096 ≤ 0xFFFFFFFFFFFF)
    (hh48 : w2.C.hwm * 4096 ≤ 0xFFFFFFFFFFFF)
    (htC : treeOK w2.C) (hok2 : wdbOK' fr w2) (hwf2 : w2.fl.WF) (hok4 : wdbOK' fr w4)
    (hwf4 : w4.fl.WF) (hfb4 : flBelow w4.fl w4.C (some (w4.C.txid + 1)))
    (htx2 : w2.C.txid + 2 < 2 ^ 64)
    (hnp : ∀ s ∈ treeSlots (spillC X2 w2.C.pages), s ∉ pendSlots w2.fl)
    (hmc : markCov X2 w2.C.hwm)
    (hal4 : ∀ x a, w4.fl.allocs !! x = some a → a.toNat ≤ w4.C.txid + 1) :
    cmPubPre D (X4.setFlPage id4 (flPageBytes w4.fl id4 (flCount w2.fl))) w4 :=
  cmPubPre_commitFl D X1 X2 X3 X4 w2.noFl w4.noFl fl1 txid0 p4 id4 hsp hD hbufs hX3pm hX3bf hX3pg
    hroot3 htxid3 hmg hvr hps hal (by rw [noFl_C, noFl_C, hC4]) htxC hCh hml hh48 htC
    (wdbOK'_noFl fr w2 hok2) hwf2 (wdbOK'_noFl fr w4 hok4) hwf4 hfb4 htx2 hnp hmc hal4

end pure

end bbolt
end EtcdGrove
end Perennial
