variables a b c d e : Prop
variable p : Prop → Prop

theorem thm₂ (h : a ↔ b) (h₁ : p a) : p b :=
propext h ▸ h₁

theorem thm2_propext_equivalence : ((a ↔ b) → p a → p b) ↔ ((a ↔ b) → a = b) :=
begin
    apply iff.intro,
        { intros hthm2 hequiv,
          exact propext hequiv }, -- is there another way?
    intros hpropext hequiv hpa,
    have : a = b, from hpropext hequiv,
    exact eq.rec hpa this
end

#print axioms thm₂
#print axioms thm2_propext_equivalence

#check @equivalence
