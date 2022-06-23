struct S
{
  int x, y;
} global;

void my_function1(void)
  __CPROVER_assigns(global) // passes
{
  global.x = 10;
  global.y = 10;
}

void my_function2(void)
  __CPROVER_assigns(global.x) // passes
{
  global.x = 10;
}

void my_function3(void)
  __CPROVER_assigns(global.y) // passes
{
  global.y = 10;
}

void my_function4(void)
  __CPROVER_assigns(global.y) // fails
{
  global.x = 10;
}
