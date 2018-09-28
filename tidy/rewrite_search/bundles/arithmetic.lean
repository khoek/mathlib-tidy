import tidy.rewrite_search.discovery.bundle

namespace tidy.rewrite_search.discovery

@[bundle] meta def arithmetic : bundle := {}

attribute [search arithmetic] add_comm add_assoc
attribute [search arithmetic] mul_comm mul_assoc mul_one
attribute [search arithmetic] left_distrib right_distrib

end tidy.rewrite_search.discovery