/- Lean-first (no Rocq counterpart).

# `work`'s proof

`below(9)` operations, each `below(7)`'s section, one credit of the id counter each (spent or not).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.work
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.below
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.echo
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.fail
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.meta_
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.canceled
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.serverStream
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.clientStream
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.bidi

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]
variable [pkg_wr : google_golang_org.protobuf.types.known.wrapperspb.Assumptions]

theorem work.wp_proof (wp_below : below.spec (GF := GF) (hG := hG))
    (wp_echo : echo.spec (GF := GF) (hG := hG)) (wp_fail : fail.spec (GF := GF) (hG := hG))
    (wp_meta : «meta».spec (GF := GF) (hG := hG)) (wp_canceled : canceled.spec (GF := GF) (hG := hG))
    (wp_serverStream : serverStream.spec (GF := GF) (hG := hG))
    (wp_clientStream : clientStream.spec (GF := GF) (hG := hG))
    (wp_bidi : bidi.spec (GF := GF) (hG := hG)) :
    work.spec (GF := GF) (hG := hG) := by
  intro γid γb c ids
  wp_start as ⟨#Hc, Htoks⟩
  wp_auto
  wp_apply wp_below (W64 9) as %ops %Hops
  have hops : uint.Z ops < 9 := Hops.2 (by decide)
  try wp_auto
  ihave HI : iprop(∃ (k : w64), "i" ∷ i_ptr ↦ k ∗ "Ht" ∷ ownToks γb (8 - uint.nat k) ∗
      "%Hk" ∷ ⌜uint.Z k ≤ uint.Z ops⌝) $$ [i Htoks]
  · iexists W64 0
    rw [show 8 - uint.nat (W64 0) = 8 by word]
    iframe
    ipureintro; word
  wp_for HI
  wp_if_destruct
  · have hk : uint.Z k < uint.Z ops := by first | word | simpa using Hif | (simp at Hif; word)
    have hsplit : 8 - uint.nat k = (8 - uint.nat (k + W64 1)) + 1 := by word
    rw [hsplit]
    icases (ownToks_add_1 1 (8 - uint.nat (k + W64 1)) γb) $$ Ht with ⟨Ht, Ht1⟩
    try wp_auto
    wp_apply wp_below (W64 7) as %sw -
    try wp_auto
    wp_if_destruct
    · try wp_auto
      wp_apply wp_echo γid γb c ids $$ [$Hc $Ht1]
      try wp_auto
      wp_for_post
      iframe
      iexists (k + W64 1)
      iframe Ht i
      ipureintro; word
    · try wp_auto
      wp_if_destruct
      · try wp_auto
        wp_apply wp_fail γid γb c ids $$ [$Hc $Ht1]
        try wp_auto
        wp_for_post
        iframe
        iexists (k + W64 1)
        iframe Ht i
        ipureintro; word
      · try wp_auto
        wp_if_destruct
        · try wp_auto
          wp_apply wp_meta γid γb c ids $$ [$Hc]
          try wp_auto
          wp_for_post
          iframe
          iexists (k + W64 1)
          iframe Ht i
          ipureintro; word
        · try wp_auto
          wp_if_destruct
          · try wp_auto
            wp_apply wp_canceled γid γb c ids $$ [$Hc $Ht1]
            try wp_auto
            wp_for_post
            iframe
            iexists (k + W64 1)
            iframe Ht i
            ipureintro; word
          · try wp_auto
            wp_if_destruct
            · try wp_auto
              wp_apply wp_serverStream γid γb c ids $$ [$Hc]
              try wp_auto
              wp_for_post
              iframe
              iexists (k + W64 1)
              iframe Ht i
              ipureintro; word
            · try wp_auto
              wp_if_destruct
              · try wp_auto
                wp_apply wp_clientStream γid γb c ids $$ [$Hc]
                try wp_auto
                wp_for_post
                iframe
                iexists (k + W64 1)
                iframe Ht i
                ipureintro; word
              · try wp_auto
                wp_apply wp_bidi γid γb c ids $$ [$Hc]
                try wp_auto
                wp_for_post
                iframe
                iexists (k + W64 1)
                iframe Ht i
                ipureintro; word
  · try wp_auto
    iapply HΦ
    itrivial

end proof

end github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver
end Perennial
