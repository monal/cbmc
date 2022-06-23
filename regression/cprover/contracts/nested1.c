void callee(int *p)
  __CPROVER_requires(__CPROVER_rw_ok(p))
{
}

void caller(int *p)
  __CPROVER_requires(__CPROVER_rw_ok(p))
{
  int i;
  __CPROVER_assert(__CPROVER_rw_ok(p), "property 1");
  callee(&i);
}
