int global;
_Bool flag;

void my_function1()
  __CPROVER_assigns(flag: global) // passes
{
  if(flag)
    global = 10;
}

void my_function2()
  __CPROVER_assigns(flag: global) // fails
{
  global = 10;
}
