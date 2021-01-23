(*Criando tipo booleano*)
Inductive bool : Type :=
  |true : bool
  |false : bool.

(*Definindo operação negação booleano*)
Definition negbool (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

(*Definindo operação injunção booleanos*)
Definition andbool (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

(*Definindo operação disjunção booleanos*)
Definition orbool (b1:bool) (b2:bool) : bool :=
  match b1 with
  |true => true
  |false => b2
  end.

(*Vamos verificar alguns valores*)
Compute (orbool true false).
Compute (andbool false true).
Compute (negbool false).

(*Agora, vamos ver se nossos exemplos (teoremas, lemas) estão corretos*)
Example test_andbool: (andbool true false) = false.
  Proof.
    reflexivity.
  Qed.

Example test_orbool: (orbool true false) = true.
  Proof.
    reflexivity.
  Qed.

Example test_negbool: (negbool (negbool false)) = false.
  Proof.
    reflexivity.
  Qed.

(*Let's create some nice notations for our brand new type*)
Notation "x && y" := (andbool x y).
Notation "x || y" := (orbool x y).

(*Let's test then*)
Example ornotat_test: false || true || false = true.
Proof.
  reflexivity.
Qed.
Example andnotat_test: true && false && true = false.
Proof.
  simpl.
  reflexivity.
Qed.
