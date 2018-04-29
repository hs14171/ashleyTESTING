%% checks array a elements 1-k, sets x to the largest element
{true}
j := 0;
% so vacuously:
{forall i (i<j->a[i]<=x)} % this is the loop invariant
while !j=k do (
	% strengthen to ignore !j=k
	{forall i (i<j->a[i]<=x)}
	if a[j]>x
	then
		% if forall i (i<j->a[i]<=x) and x<a[j], then:
		{forall i (i<j->a[i]<=a[j])}
		x := a[j]
	else
		skip;

	{forall i (i<j->a[i]<=x) & a[j]<=x}
	% this means that:
	{forall i (i<j+1->a[i]<=x)}
	j := j+1
	{forall i (i<j->a[i]<=x)}
)
{forall i (i<j -> a[i]<=x) & j=k}
{forall i (i<k -> a[i]<=x)}%