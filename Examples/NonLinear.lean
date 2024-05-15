import IIT

mutual

iit A : Type where
| a0 : A
| a1 : A

iit B : (a a' : A) → Type where
| foo : (a : A) → B a a

iit_termination
  all_goals sorry
end

#print B.w
