From mathcomp Require Export fintype finset ssrbool.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module nonEmptyFintype.

  Section Def.


    Record mixin_of (T : finType) := Mixin {
      default : T;
    }.
    Structure class_of (T : finType):= Class {
      base : Finite.class_of T;
      mixin : mixin_of T
    }.
    Structure type := Pack {
      sort : finType ;
      class_ : class_of sort
    }.

  End Def.

  Section nonEmptyFintype_of.

    Variable T : finType.
    Variable x : T.

    Definition nonEmptyFinType_of : type :=
      {|
        sort := T;
        class_ := {|
          base := Finite.class T;
          mixin := {| default := x |}
        |};
      |}.

  End nonEmptyFintype_of.


  Module Exports.
    Coercion base : class_of >-> Finite.class_of.
    Coercion sort : type >-> finType.
    Notation nonEmptyFintype := nonEmptyFintype.type.
    Notation default T := (default (mixin (class_ T))).
    Notation nonEmptyFinType_of := nonEmptyFintype.nonEmptyFinType_of.

  End Exports.

End nonEmptyFintype.

Export nonEmptyFintype.Exports.


Module nonEmptyFinset.

  Section Def.

    Variable T : nonEmptyFintype.

    Structure type := Pack {
      carrier : {set T};
      hasDefault : default T \in carrier;
    }.

  End Def.

  Module Exports.
    Notation nonEmptyFinset := nonEmptyFinset.type.
    Notation hasDefault := nonEmptyFinset.hasDefault.
    Coercion carrier : type >-> set_of.
    Notation "{ 'SET' T }" := (nonEmptyFinset T).

  End Exports.

  End nonEmptyFinset.

Export nonEmptyFinset.Exports.






