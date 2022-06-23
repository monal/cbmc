int x, y;

void my_function()
  __CPROVER_ensures(x == 10) // passes
  __CPROVER_ensures(y == 20) // fails
  __CPROVER_assigns(x, y)
{
  x = 10;
  y = 10;
}
