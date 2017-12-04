# Zsyntax automated theorem prover
## Build instructions
### macOS
* Install the Haskell Platform (https://www.haskell.org/platform/)
* Install Gtk (as in this guide: https://wiki.haskell.org/Gtk2Hs/Mac)
* Build the application using the `stack` build tool:

```
$ stack install alex happy
$ stack install gtk2hs-buildtools
$ stack install glib
$ stack build --flag gtk:have-quartz-gtk
```

## Execution

```
$ stack exec zsyntax-exe
```