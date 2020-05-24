
namespace hidden
    instance inhabited_sum (α : Type) (β : Type) [inhabited α] : inhabited (α ⊕ β) :=
    ⟨@sum.inl α β (default α)⟩

    instance inhabited_nonempty (α : Type) [inhabited α] : inhabited (list α) :=
    ⟨list.cons (default α) list.nil⟩


    def add_lists (α : Type) [has_add α] : list α → list α → list α
    | [] [] := []
    | l1 [] := l1
    | [] l2 := l2
    | (hd1::tl1) (hd2::tl2) := (hd1 + hd2)::(add_lists tl1 tl2)

    instance list_has_add (α : Type) [has_add α] : has_add (list α) :=
    ⟨add_lists α⟩

    example : [3, 2] + [] = [3, 2] := rfl
    example : [] + [3, 2] = [3, 2] := rfl
    example : (@list.nil ℕ) + [] = [] := rfl
    example : [3, 2] + [10, 20] = [13, 22] := rfl

end hidden
