CM.make();
Make_spec.make_spec "bst_del.spec";
use "bst_del.spec.sml";
structure G = GFn(spec);
G.start();
