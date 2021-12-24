/*!
  \file aig_algebraic_rewriting.hpp
  \brief AIG algebraric rewriting
  EPFL CS-472 2021 Final Project Option 1
*/

#pragma once

#include "../networks/aig.hpp"
#include "../views/depth_view.hpp"
#include "../views/topo_view.hpp"
#include "../utils/debugging_utils.hpp"

namespace mockturtle
{

namespace detail
{

template<class Ntk>
class aig_algebraic_rewriting_impl
{
  using node = typename Ntk::node;
  using signal = typename Ntk::signal;

public:
  aig_algebraic_rewriting_impl( Ntk& ntk )
    : ntk( ntk )
  {
    static_assert( has_level_v<Ntk>, "Ntk does not implement depth interface." );
  }

  void run()
  {
    bool cont{true}; /* continue trying */
    while ( cont )
    {
      cont = false; /* break the loop if no updates can be made */
      ntk.foreach_gate( [&]( node n ){
        if ( try_algebraic_rules( n ) )
        {
          ntk.update_levels();
          cont = true;
        }
      });
    }
  }

private:
  /* Try various algebraic rules on node n. Return true if the network is updated. */
  bool try_algebraic_rules( node n )
  {


    if ( try_associativity( n ) )
      return true;
    if ( try_distributivity( n ) )
      return true;
    if(try_three_layer_distributivity(n))
      return true;
    /* TODO: add more rules here... */

    return false;
  }


  bool try_associativity(node n)
  {

    if(ntk.is_on_critical_path(n) && ntk.level(n) > 1)
    {
      //Primary Checks is Associativity even useful / possible?
      std::vector<signal> critical , noncritical;
      uint32_t nonCriticalLevel;

      ntk.foreach_fanin(n, [&](signal const& child){

        node childnode = ntk.get_node(child);

        if(ntk.is_on_critical_path(childnode) && !ntk.is_complemented(child))
        {
          ntk.foreach_fanin(childnode, [&](signal const& grandchild){
            node grandchildnode = ntk.get_node(grandchild);
            if(ntk.is_on_critical_path(grandchildnode))
            {
              critical.push_back(grandchild);
            }
            else
            {
              noncritical.push_back(grandchild);
            }
          });
        }
        else
        {
          noncritical.push_back(child);
          nonCriticalLevel = ntk.level(childnode);
        }

      });

      if(critical.size() == 1 && noncritical.size() == 2)
      {
        node criticalNode = ntk.get_node(critical[0]);
        
        if(nonCriticalLevel < ntk.level(criticalNode))
        { 
          
           signal subNode = ntk.create_and(critical[0], ntk.create_and(noncritical[0], noncritical[1]));
           ntk.substitute_node(n, subNode);

           return true;          
        }

      }

    }

    return false;
  }


  /* Try the distributivity rule on node n. Return true if the network is updated. */
  bool try_distributivity(node n)
  {
    if(ntk.is_on_critical_path(n) && ntk.level(n) > 1)
    {
      std::vector<signal> nonCriticalGrandChildren, criticalGrandChildren;

      ntk.foreach_fanin(n, [&](signal const& child){

        node childnode = ntk.get_node(child);

        if(ntk.is_on_critical_path(childnode)&&ntk.is_complemented(child))
        {
            ntk.foreach_fanin(childnode, [&](signal const& grandchild){
              node grandchildnode = ntk.get_node(grandchild);

              if(ntk.is_on_critical_path(grandchildnode))
              {
                criticalGrandChildren.push_back(grandchild);
              }else{
                nonCriticalGrandChildren.push_back(grandchild);
              }

            });
        }

      });

      if(criticalGrandChildren.size() == 2 && nonCriticalGrandChildren.size() == 2)
      {
        if(criticalGrandChildren[0] == criticalGrandChildren[1])
        {
          signal subNode = ntk.create_nand(criticalGrandChildren[0],ntk.create_or(nonCriticalGrandChildren[0],nonCriticalGrandChildren[1]));
          if(ntk.is_or(n))
            subNode = ntk.create_not(subNode);
          
          ntk.substitute_node(n,subNode);
          return true;
      }

      }

    }

    return false;
}

bool try_three_layer_distributivity(node n)
{
      if (ntk.is_on_critical_path( n ))
      {
        std::vector<signal> nonCriticalChildren, criticalChildren;
        std::vector<signal> nonCriticalGrandChildren, criticalGrandChildren;
        std::vector<signal> nonCriticalGranderChildren, criticalGranderChildren;


        ntk.foreach_fanin(n, [&](signal const& child){

          node childnode = ntk.get_node(child);

          if(ntk.is_on_critical_path(childnode)&&ntk.is_complemented(child))
          {
            criticalChildren.push_back(child);

            ntk.foreach_fanin(childnode, [&](signal const& grandChild){

              node grandChildNode = ntk.get_node(grandChild);

              if(ntk.is_on_critical_path(grandChildNode)&&ntk.is_complemented(grandChild))
              {
                criticalGrandChildren.push_back(grandChild);

                ntk.foreach_fanin(grandChildNode, [&](signal const& granderChild){
                
                  node granderChildNode = ntk.get_node(granderChild);

                  if(ntk.is_on_critical_path(granderChildNode))
                  {
                    criticalGranderChildren.push_back(granderChild);
                  }
                  else
                  {
                    nonCriticalGranderChildren.push_back(granderChild);
                  }

                });//granderchild foreach

              }
              else
              {
                nonCriticalGrandChildren.push_back(grandChild);
              }

            });//grandchild foreach

          }else{
            nonCriticalChildren.push_back(child);
          }

        });//child foreach


        if(nonCriticalChildren.size() == 1 && criticalChildren.size() == 1 && 
            nonCriticalGrandChildren.size() == 1 && criticalGrandChildren.size() == 1 && 
              nonCriticalGranderChildren.size() == 1 && criticalGranderChildren.size() == 1)
        {

          node top_crit_node = ntk.get_node(criticalChildren[0]);
          node top_noncrit_node = ntk.get_node(nonCriticalChildren[0]);
          if(ntk.level(top_crit_node) - ntk.level(top_noncrit_node)  >=  2)
          {
            signal node_bir , node_iki , subNode;

            node_bir = ntk.create_not(ntk.create_and(criticalGranderChildren[0],ntk.create_and(nonCriticalChildren[0],nonCriticalGranderChildren[0])));
            node_iki = ntk.create_not(ntk.create_and(nonCriticalChildren[0], ntk.create_not(nonCriticalGrandChildren[0])));
            subNode  = ntk.create_nand(node_bir,node_iki);

            ntk.substitute_node(n, subNode);
            return true;
          }
        }

      }


  return false;
}

private:
  Ntk& ntk;
};

} // namespace detail

/* Entry point for users to call */
template<class Ntk>
void aig_algebraic_rewriting( Ntk& ntk )
{
  static_assert( std::is_same_v<typename Ntk::base_type, aig_network>, "Ntk is not an AIG" );

  depth_view dntk{ntk};
  detail::aig_algebraic_rewriting_impl p( dntk );
  p.run();
}

} /* namespace mockturtle */