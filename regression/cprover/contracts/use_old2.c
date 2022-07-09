void my_function(unsigned parameter)
  __CPROVER_requires(1)
{
  for(unsigned counter = 0; counter != 100; counter++)
  {
    __CPROVER_assert(parameter == __CPROVER_old(parameter), "property 1");
  }

  __CPROVER_assert(parameter == __CPROVER_old(parameter), "property 2");
}
