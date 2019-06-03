
## University tasks written in prolog

Those are three projects written in prolog.

In the names of files and catalogs mentioned below you would have to replace `N` with number 1, 2 or 3.

Files `pracN.pl` and `pracN.pdf` are written by employees of Institute of Computer Science of University of Wroclaw.

Every catalog `pracowniaN` contains:
 * description of the task in file `pracN.pdf` in Polish
 * solution of the task in file `bohdan_shcherbak.pl`
 * tests in file `bohdan_shcherbak_tests.pl`
 * checker in file `pracN.pl` which runs the tests on the solution

In order to run the tests you have to intall [swi-prolog](http://www.swi-prolog.org/) and execute the following commands in the command line:

```
$ swipl pracN.pl
```
and then run
```
?- test_all.
```
