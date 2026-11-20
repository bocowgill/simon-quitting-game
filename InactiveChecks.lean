module
public import InactiveShard0
public import InactiveShard1
public import InactiveShard2
public import InactiveShard3
public import InactiveShard4
public import InactiveShard5
public import InactiveShard6
public import InactiveShard7

/-! # Finite assembly of the 464 verified base phases -/

@[expose] public section
namespace PalomarSimon.Inactive

theorem verified (t : Fin 464) (i : Fin 4) : rowOK t.val i = true := by
  have groups (k : Fin 29) : groupOK k.val := by
    fin_cases k
    · exact group0
    · exact group1
    · exact group2
    · exact group3
    · exact group4
    · exact group5
    · exact group6
    · exact group7
    · exact group8
    · exact group9
    · exact group10
    · exact group11
    · exact group12
    · exact group13
    · exact group14
    · exact group15
    · exact group16
    · exact group17
    · exact group18
    · exact group19
    · exact group20
    · exact group21
    · exact group22
    · exact group23
    · exact group24
    · exact group25
    · exact group26
    · exact group27
    · exact group28
  let k : Fin 29 := ⟨t.val / 16, by have := t.isLt; omega⟩
  let j : Fin 16 := ⟨t.val % 16, Nat.mod_lt _ (by decide)⟩
  have e : 16*k.val + j.val = t.val := Nat.div_add_mod _ _
  rw [← e]
  exact groups k j i

end PalomarSimon.Inactive

