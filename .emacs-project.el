(list (cons 'include-dirs
	    (list (concat (file-name-as-directory project-dir) "src/include")))
      (cons 'cxxflags
	    (list "-Wno-mismatched-tags")))
