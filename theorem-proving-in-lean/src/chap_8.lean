namespace chap8ex1

    open function

    #print surjective

    universes u v w
    variables {α : Type u} {β : Type v} {γ : Type w}
    open function

    lemma composition_check {g : β → γ} {f : α → β} : α → γ := g ∘ f

    lemma surjective_comp {g : β → γ} {f : α → β} (hg : surjective g) (hf : surjective f) :
    surjective (g ∘ f) :=
    λ lg,
    match (hg lg) with exists.intro (b: β) (beq : g b = lg) :=
        match (hf b) with exists.intro (a : α) (aeq : f a = b) :=
            begin
                existsi a,
                simp [aeq, beq]
            end
        end
    end

end chap8ex1
