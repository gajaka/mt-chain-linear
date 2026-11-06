/-
  A noninjective quotient with edges that survive projection.

  The four subsets of Fin 2 form a diamond under inclusion. Certification
  depends on cardinality, so its two incomparable middle elements merge.
  Strict inclusions increase cardinality and therefore never collapse.
  The fixed datum 0 is certified at every source vertex; other data distinguish
  the three quotient classes. This discharges the noncollapse obligation of
  Certification.QuotientBridge rather than assuming it.

  For the diamond and its rank order, see Davey and Priestley,
  Introduction to Lattices and Order, second edition, Cambridge, 2002.
-/
module

public import PPGraph.Certification.QuotientBridge

@[expose] public section

namespace CertifiedQuotientExample

abbrev Spec := Finset (Fin 2)

def cardinalityCertificate : Certificate Nat Spec := fun d s => d ≤ s.card

def family : CertFamily Nat Spec where
  certs := [cardinalityCertificate]
  all_monotone := by
    intro C hC
    simp only [List.mem_singleton] at hC
    subst C
    intro d s t hst hds
    exact le_trans hds (Finset.card_le_card hst)

theorem fully_certified_iff (d : Nat) (s : Spec) :
    fully_certified family d s ↔ d ≤ s.card := by
  simp [fully_certified, family, cardinalityCertificate]

theorem certificate_equiv_iff_card (s t : Spec) :
    cert_equiv family s t ↔ s.card = t.card := by
  constructor
  · intro h
    have hst : s.card ≤ t.card :=
      (fully_certified_iff s.card t).mp
        ((h s.card).mp ((fully_certified_iff s.card s).mpr le_rfl))
    have hts : t.card ≤ s.card :=
      (fully_certified_iff t.card s).mp
        ((h t.card).mpr ((fully_certified_iff t.card t).mpr le_rfl))
    exact le_antisymm hst hts
  · intro h d
    simp only [fully_certified_iff, h]

theorem edges_separate : certified_edges_separate_classes family 0 := by
  intro s t he hsame
  have hlt : s.card < t.card :=
    Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨he.1.1, he.1.2⟩)
  exact (Nat.ne_of_lt hlt) ((certificate_equiv_iff_card s t).mp hsame)

def project (s : Spec) : SpecQuotient family := Quotient.mk (certSetoid family) s

theorem projection_pp_quotient :
    pp_quotient project (certified_subgraph Spec family 0)
      (certified_quotient_graph family 0)
      spec_rr (fully_certified family 0) (fun q1 q2 : SpecQuotient family => q1 ≤ q2)
      (quotient_certified family 0) :=
  certified_proj_is_pp_quotient family 0 edges_separate

theorem different_middles_merge : project {0} = project {1} := by
  exact Quotient.sound ((certificate_equiv_iff_card {0} {1}).mpr (by decide))

theorem projection_not_injective : ¬ Function.Injective project := by
  intro h
  have heq : ({0} : Spec) = {1} := h different_middles_merge
  exact (by decide : ({0} : Spec) ≠ {1}) heq

theorem projected_edge_of_strict_subset (s t : Spec) (hst : s ⊂ t) :
    (certified_quotient_graph family 0).edges (project s) (project t) := by
  have hs : fully_certified family 0 s := (fully_certified_iff 0 s).mpr (Nat.zero_le _)
  have he : (certified_subgraph Spec family 0).edges s t :=
    ⟨Finset.ssubset_iff_subset_ne.mp hst, hs⟩
  exact (projection_pp_quotient.1.2 s t
    ⟨he, certified_subgraph_pp_valid family 0 s t he⟩).1

theorem quotient_has_two_edges :
    (certified_quotient_graph family 0).edges (project ∅) (project {0}) ∧
    (certified_quotient_graph family 0).edges (project {0}) (project {0, 1}) := by
  constructor
  · exact projected_edge_of_strict_subset ∅ {0} (by decide)
  · exact projected_edge_of_strict_subset {0} {0, 1} (by decide)

end CertifiedQuotientExample

#check @CertifiedQuotientExample.fully_certified_iff
#check @CertifiedQuotientExample.certificate_equiv_iff_card
#check @CertifiedQuotientExample.edges_separate
#check @CertifiedQuotientExample.projection_pp_quotient
#check @CertifiedQuotientExample.different_middles_merge
#check @CertifiedQuotientExample.projection_not_injective
#check @CertifiedQuotientExample.projected_edge_of_strict_subset
#check @CertifiedQuotientExample.quotient_has_two_edges
