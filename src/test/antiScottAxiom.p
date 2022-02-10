%------------------------
% Formula  : AntiScott1
% Status   : unprovable
%------------------------

fof(ax, axiom, (
(   ( ( ~ (~ a)) => a) =>  ( ~(~ a) | ~a ) )   =>  ( ~ (~ a) |  ~a)
)).

fof(conj, conjecture, (
(    (~ (~ a) => a) | ~( ~ a) )
)).
%------------------------
