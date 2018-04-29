% Euclidean division -- finds q and r such that x=q*y+r & 0<=r<y
% A program doesn't need to be fully annotated, one can give just loop invariants and pre/postcondition

{ x>=0 & y>0  }
q:=0;
r:=x;
{ x=q*y+r & q>=0 & r>=0 & y>0 } % the loop invariant
while r>=y do (
	r:=r-y;
	q:=q+1
)
% now we have the loop invariant and !r>=y:
{x=q*y+r & q>=0 & r>=0 & r<y}