
Generalizable All Variables.




Inductive term {Action:Type} {Time:Type} : Type :=
| EmptyProcess : term  
| StartWithDuration : Action -> Time -> term
| Sequence : Action -> term -> term
| Offset : Time -> term -> term
| Delay : term -> term
| DelayElim : term -> term
| Choice : term -> term -> term
| Fork : term -> term -> term.
