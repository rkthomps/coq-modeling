Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.

Fixpoint min (l : (list nat)) : option nat := 
    match l with
    | nil => None
    | h :: tl => match (min tl) with
        | None => Some h 
        | Some m => if (h <? m) then (Some h) else (Some m)
        end
    end.

Lemma exists_min: forall (l : (list nat)), 
    (l <> nil) -> exists h, min(l) = Some(h).
induction l; intuition; simpl in *.                                                                                                                            
destruct l; simpl in *.                                                                                                                                        
econstructor.                                                                                                                                                  
exfalso.                                                                                                                                                       
eapply H.                                                                                                                                                      
eapply eq_sym.                                                                                                                                                 
destruct a.                                                                                                                                                    
exfalso.                                                                                                                                                       
eapply not_eq_sym.                                                                                                                                             
eapply nil_cons.                                                                                                                                               
exfalso.                                                                                                                                                       
eapply not_eq_sym.                                                                                                                                             
eapply nil_cons.                                                                                                                                               
exfalso.        
Admitted.