Message à l'intention de MM. Tronel et Wilke

Une errue apparaît lors de la compilation ; 

File "ltl_debug.ml", line 222, characters 37-40:
222 |     Conduit_lwt_unix.endp_to_server ~ctx endp >>= fun server ->
                                           ^^^
Error: This expression has type
         Conduit_lwt_unix.ctx Lazy.t = Conduit_lwt_unix.ctx lazy_t
       but an expression was expected of type Conduit_lwt_unix.ctx
Command exited with code 2.


Cela ne figure pas dans les fonctions à compléter, je ne suis pas certain de comprendre comment la faire fonctionner et comment permettre ainsi au compilateur de générer le fichier test/result.html.