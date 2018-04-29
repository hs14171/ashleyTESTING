% Euclidean division -- finds q and r such that x=q*y+r & 0<=r<y

{ x>=0 & y>0 }
q:=0;
{ x=q*y+x & q>=0 & x>=0 & y>0 }
r:=x;
{ x=q*y+r & q>=0 & r>=0 & y>0 } % the loop invariant
while r>=y do (
	% strengthen to a statement explictly with 'r-y'
	{ x=(q+1)*y+r-y & q>=0 & y>0 & r-y>=0 }
	r:=r-y;
	{ x=(q+1)*y+r & q>=0 & y>0 & r>=0 }
	% strengthen again to 'q+1>=0'
	{ x=(q+1)*y+r & q+1>=0 & y>0 & r>=0}
	q:=q+1
)
% now we have the loop invariant and !r>=y:
{ x=q*y+r & q>=0 & r>=0 & r<y }
