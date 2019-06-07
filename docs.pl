:- use_module(library(doc_files)).
:- consult('src/dfs_main.pl').
:- write('Generating documentation ...\n').
:- doc_save(src, [recursive(true), doc_root(docs), title='DFS Tools']).
:- halt.
