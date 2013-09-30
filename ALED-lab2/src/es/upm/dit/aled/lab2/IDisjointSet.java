package es.upm.dit.aled.lab2;

public interface IDisjointSet {

    /**
     * Searches for the group of the given item.
     * 
     * @param item The item for whose group to look for.
     * @return The item at the root of the group, in which the given item is
     *         found.
     */
    public int find(int item);
    
    /**
     * Joins the groups of the two items.
     * 
     * @param item1 The first item to join.
     * @param item2 The second item to join.
     * @return The root of the joint group.
     */
    public int join(int item1, int item2);

    /**
     * @return The number of groups in the set.
     */
    public int size();
    
}