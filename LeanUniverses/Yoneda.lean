structure SmallCat where
  Obj : Type
  Mor : Obj → Obj → Type
  id  (x : Obj) :  Mor x x
  comp {x y z : Obj} (f : Mor y z) (g : Mor x y) : Mor x z
  assoc {w x y z : Obj} (h : Mor y z) (g : Mor x y) (f : Mor w x) :
    comp (comp h g) f = comp h (comp g f)
  left_id {x y : Obj} (f : Mor x y) : comp (id y) f = f
  right_id {x y : Obj} (f : Mor x y) : comp f (id x) =f


structure BigCat where
  Obj : Type 1
  Mor : Obj → Obj → Type
  id  (x : Obj) :  Mor x x
  comp {x y z : Obj} (f : Mor y z) (g : Mor x y) : Mor x z
  assoc {w x y z : Obj} (h : Mor y z) (g : Mor x y) (f : Mor w x) :
    comp (comp h g) f = comp h (comp g f)
  left_id {x y : Obj} (f : Mor x y) : comp (id y) f = f
  right_id {x y : Obj} (f : Mor x y) : comp f (id x) = f

def TypeCat : BigCat where
  Obj := Type
  Mor X Y := X → Y
  id X := fun x => x
  comp g f := fun x => g (f x)
  assoc _ _ _ := by rfl
  left_id _ := by rfl
  right_id _ := by rfl

def op (C : SmallCat) : SmallCat where
  Obj := C.Obj
  Mor x y := C.Mor y x
  id := C.id
  comp f g := C.comp g f
  assoc h g f := (C.assoc f g h).symm
  left_id f := (C.right_id f)
  right_id f := (C.left_id f)

structure Funct (C D : SmallCat) where
  map_ob : C.Obj → D.Obj
  map_mor {x y : C.Obj} (f : C.Mor x y) : D.Mor (map_ob x) (map_ob y)
  map_id {x : C.Obj} : map_mor (C.id x) = D.id (map_ob x)
  map_comp {x y z : C.Obj} (g : C.Mor y z) (f : C.Mor x y) : map_mor (C.comp g f) = D.comp (map_mor g) (map_mor f)

structure NatTrans {C D : SmallCat} (F G : Funct C D) where
  app (x : C.Obj) : D.Mor (F.map_ob x) (G.map_ob x)
  nat {x y : C.Obj} (f : C.Mor x y) :
    D.comp (app y) (F.map_mor f) = D.comp (G.map_mor f) (app x)

def NatTransId {C D : SmallCat} (F : Funct C D) : NatTrans F F where
  app x := D.id (F.map_ob x)
  nat f := by rw [D.left_id, D.right_id]

def NatTransComp {C D : SmallCat} (F G H : Funct C D) (α : NatTrans F G) (β : NatTrans G H) : NatTrans F H where
  app x := D.comp (β.app x) (α.app x)
  nat f := by sorry
