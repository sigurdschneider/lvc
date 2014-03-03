Require Import Util DecidableTactics Get.


Ltac dec_solve := solve [ left; econstructor; eauto 
                        | let H := fresh "H" in right; intro H; inv H; repeat get_functional; isabsurd; eauto ].

