void my_function1(int *parameter)
  __CPROVER_requires(__CPROVER_w_ok(parameter))
  __CPROVER_assigns(*parameter) // passes
{
  *parameter = 10;
}

void my_function2(int *parameter)
  __CPROVER_requires(__CPROVER_w_ok(parameter))
  __CPROVER_assigns() // fails
{
  *parameter = 10;
}

void my_function3(int *parameter)
  __CPROVER_requires(__CPROVER_w_ok(parameter))
  // implicit assigns clause fails
{
  *parameter = 10;
}
