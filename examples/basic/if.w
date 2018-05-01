% proof of an if statement
% this program sets m to max(a,b)
{true}
if a>b
then
    {a>=b} % need to strengthen precondition, a>b -> a>=b
    m:=a
else
    m:=b;

{ ( m=a & m>=b ) || ( m=b & m>=a ) }