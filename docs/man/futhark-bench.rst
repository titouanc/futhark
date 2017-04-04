.. role:: ref(emphasis)

.. _futhark-bench(1):

=============
futhark-bench
=============

SYNOPSIS
========

futhark-bench [--runs=count | --compiler=program | --json | --no-validate] programs...

DESCRIPTION
===========

This program is used to benchmark Futhark programs.  In addition to
the notation used by ``futhark-test(1)``, this program also supports
the dataset keyword ``nobench``.  This is used to indicate datasets
that are worthwhile for testing, but too small to be worth
benchmarking.

Programs are compiled using the specified compiler (``futhark-c`` by
default), then run a number of times for each data set, and the
average runtime printed on standard output.  A program will be ignored
if it contains no data sets - it will not even be compiled.  Only data
sets that use the default entry point (``main``) are considered.

If compilation or running fails, an error message will be printed and
benchmarking will continue, but a non-zero exit code will be returned
at the end.

OPTIONS
=======

--runs=count

  The number of runs per data set.

--compiler=program

  The program used to compile Futhark programs.  This option can be
  passed multiple times, resulting in multiple compilers being used
  for each test case.  The specified program must support the same
  interface as ``futhark-c``.

--json=file

  Write raw results in JSON format to the specified file.

--pass-option=opt

  Pass an option to benchmark programs that are being run.  For
  example, we might want to run OpenCL programs on a specific device::

    futhark-bench prog.fut --compiler=futhark-opencl --pass-option=-dHawaii

EXAMPLES
========

The following program benchmarks how quickly we can sum arrays of
different sizes::

  -- How quickly can we reduce arrays?
  --
  -- ==
  -- nobench input { 0 }
  -- output { 0 }
  -- input { 100 }
  -- output { 4950 }
  -- compiled input { 100000 }
  -- output { 704982704 }
  -- compiled input { 100000000 }
  -- output { 887459712 }

  let main(n: i32): i32 =
    reduce(+, 0, iota(n))

SEE ALSO
========

futhark-c(1), futhark-test(1)
