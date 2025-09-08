

/- ## リスト内表記の追加 -/

declare_syntax_cat compClause

syntax "for " term " in " term : compClause
syntax "if " term : compClause
syntax "[" term " | " compClause,* "]" : term

macro_rules
  | `([$t |]) => `([$t])
  | `([$t | for $x in $xs]) => `(List.map (fun $x => $t) $xs)
  | `([$t | if $x]) => `(if $x then [$t] else [])
  | `([$t | $c, $cs,*]) => `(List.flatten [[$t | $cs,*] | $c])

#eval [x ^ 2 | for x in [1, 2, 3, 4, 5]]
#eval List.map (fun x => x ^ 2) [1, 2, 3, 4, 5]

#eval [(x, y) | for x in [1, 2, 3], for y in [4, 5]]
#eval List.flatten [[(x, y) | for y in [4, 5]] | for x in [1, 2, 3]]

#eval [x | for x in [1, 2, 3, 4], if x < 3]
#eval List.flatten [[x | if x < 3] | for x in [1, 2, 3, 4]]
