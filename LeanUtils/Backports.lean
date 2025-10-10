import Lean

-- From Lean core, for backward compatibility with old Lean versions

def List.flatten' {α : Type} : List (List α) → List α
  | []      => []
  | l :: L => l ++ flatten' L

def Lean.Elab.InfoTree.collectNodesBottomUpM' [Monad m]
    (p : ContextInfo → Info → PersistentArray InfoTree → List α → m (List α)) (i : InfoTree) : m (List α) :=
  (·.getD []) <$> i.visitM (m := m) (postNode := fun ci i cs as => do p ci i cs (as.filterMap id).flatten')

@[inline] def List.flatMap' {α : Type} {β : Type} (b : α → List β) (as : List α) : List β := List.flatten' (List.map b as)

def List.dedup' {α : Type} [DecidableEq α] : List α → List α
  | [] => []
  | cons a l =>  if a ∈ l then l.dedup' else a :: l.dedup'
