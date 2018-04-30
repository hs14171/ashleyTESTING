% this program should set x equal to k squared

{x=x}
x:=k;
{x=k}
i:=1;
{x=i*k} % loop invariant
while !i=k do (
	{x+k=(i+1)*k}
	x := x+k;
	{x=(i+1)*k}
	i := i+1;
	);
{x=k*k & !!i=k}
{x=k*k}
