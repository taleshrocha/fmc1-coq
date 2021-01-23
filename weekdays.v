Inductive day : Type :=
  | monday : day
  | tuesday : day
  | wednesday : day
  | thursday : day
  | friday : day
  | saturday : day
  | sunday : day.

Theorem fridayIsFriday : friday = friday.
Proof.
  reflexivity.
Qed.

Definition next_weekday (d:day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => saturday 
  | saturday => sunday
  | sunday => monday
  end.

Compute (next_weekday friday).

Compute (next_weekday (next_weekday monday)).

Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = monday.
Proof.
  simpl.
  reflexivity.
Qed.
