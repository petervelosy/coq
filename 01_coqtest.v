Print nat.
Print nat_ind.

Inductive Boole : Set :=
  igaz : Boole |
  hamis : Boole.

Definition Boole_Or (b1: Boole) (b2: Boole) : Boole :=
  match b1 with
    igaz => igaz |
    hamis => b2
  end.

Notation "x 'vagy' y" := (Boole_Or x y)(at level 20) : type_scope.

Definition Boole_And (b1: Boole) (b2: Boole) : Boole :=
  match b1 with
    igaz => b2 |
    hamis => hamis
  end.

Notation "x 'és' y" := (Boole_And x y)(at level 20) : type_scope.

Definition Boole_Not (b: Boole) : Boole :=
  match b with
    igaz => hamis |
    hamis => igaz
  end.

Notation "'nem' x" := (Boole_Not x)(at level 20) : type_scope.

Check igaz vagy hamis.

Eval compute in (igaz vagy hamis).

Definition Boole_Impl (b1: Boole) (b2: Boole) : Boole :=
  match b1 with
    igaz => match b2 with
              igaz => igaz |
              hamis => hamis
            end |
    hamis => igaz
  end.

Notation "'ha' x 'akkor' y" := (Boole_Impl x y) (at level 20) : type_scope.

Eval compute in (ha hamis akkor igaz).

Definition Boole_ImplOnlyIf (b1: Boole) (b2: Boole) : Boole :=
  match b1 with
    igaz => match b2 with
              igaz => igaz |
              hamis => hamis
            end |
    hamis => hamis
  end.

Notation "'ha' x 'csakkor' y" := (Boole_ImplOnlyIf x y) (at level 20) : type_scope.

Eval compute in (ha hamis csakkor igaz).

Theorem LEM : (forall x : Boole, x vagy (nem x) = igaz).
  Proof.
    intros.
    apply Boole_ind with (P := fun x => x vagy (nem x) = igaz).
    unfold Boole_Or.
    unfold Boole_Not.
    reflexivity.
    unfold Boole_Or.
    unfold Boole_Not.
    reflexivity.
    Show Proof.
  Qed.

Theorem MZ_1 : (forall x y: Boole, ha x akkor y = (nem x) vagy y).
  Proof.
    intros.
    apply Boole_ind with (P := fun x => ha x akkor y = (nem x) vagy y).
    apply Boole_ind with (P := fun y => ha igaz akkor y = (nem igaz) vagy y).
    unfold Boole_Impl.
    unfold Boole_Not.
    unfold Boole_Or.
    reflexivity.
    unfold Boole_Impl.
    unfold Boole_Not.
    unfold Boole_Or.
    reflexivity.
    apply Boole_ind with (P := fun y => ha hamis akkor y = (nem hamis) vagy y).
    unfold Boole_Impl.
    unfold Boole_Not.
    unfold Boole_Or.
    reflexivity.
    unfold Boole_Impl.
    unfold Boole_Not.
    unfold Boole_Or.
    reflexivity.
    Show Proof.
  Qed.

Theorem DM_2 : (forall x y: Boole, (nem x) és (nem y) = nem (x vagy y)).
  Proof.
    intros.
    apply Boole_ind with (P := fun x => (nem x) és (nem y) = nem (x vagy y)).
    apply Boole_ind with (P := fun y => (nem igaz) és (nem y) = nem (igaz vagy y)).
    unfold Boole_Or.
    unfold Boole_Not.
    unfold Boole_And.
    reflexivity.
    unfold Boole_Or.
    unfold Boole_Not.
    unfold Boole_And.
    reflexivity.
    apply Boole_ind with (P := fun y => (nem hamis) és (nem y) = nem (hamis vagy y)).
    unfold Boole_Or.
    unfold Boole_Not.
    unfold Boole_And.
    reflexivity.
    unfold Boole_Or.
    unfold Boole_Not.
    unfold Boole_And.
    reflexivity.
    Show Proof.
  Qed.