package com.filetool.model;
import java.util.ArrayList;
import java.util.Stack;

import java.util.ArrayList;
import java.util.Stack;

public class Graph {
	  private ArrayList<Vertex> vertexList;
	  private int[][] edgeMatrix;//邻接矩阵
	  private int nEdgeNum;//边的数量

	  public Graph(int nVNum)
	  {
	    this.vertexList = new ArrayList<Vertex>();
	    this.edgeMatrix = new int[nVNum][nVNum];
	    for (int i = 0; i < nVNum; ++i)
	    {
	      for (int j = 0; j < nVNum; ++j)
	      {
	        this.edgeMatrix[i][j] = 0;
	      }
	    }
	    nEdgeNum=0;
	    
	  }
	  
	  //初始化建立图像,并且对边数组中边在邻接矩阵中的端点赋值
	  public void Init(ArrayList<Integer> arrayVertexId,ArrayList<Edge> arrayEdge)
	  {
			//插入顶点
			for(Integer n:arrayVertexId)
			{
				Vertex vertex=new Vertex();
				vertex.oValue=n;//真实ID
				this.AddVertex(vertex);
			}
			//插入边
			for(Edge edge:arrayEdge)
			{
				edge.nSourceIdInMatrix=arrayVertexId.lastIndexOf(edge.nSourceIdInTopo);
				edge.nDestIdInMatrix=arrayVertexId.lastIndexOf(edge.nDestIdInTopo);
				this.AddEdge(edge.nSourceIdInMatrix, edge.nDestIdInMatrix, edge.nWeight);
			}
			
	  }

	  public ArrayList<Vertex> GetVertexList()
	  {
	    return this.vertexList;
	  }

	  public int[][] GetEdgeMatrix()
	  {
	    return this.edgeMatrix;
	  }
	  
	  //获得某点的顶点值
	  public Object GetVertexValueByIndex(int nIndex)
	  {
	    if (nIndex < this.vertexList.size())
	    {
	      return ((Vertex)this.vertexList.get(nIndex)).oValue;
	    }

	    return null;
	  }

	  //获得两点之间的权重值
	  public int GetWeight(int nV1, int nV2)
	  {
	    if ((nV1 < this.edgeMatrix.length) && (nV2 < this.edgeMatrix.length))
	    {
	      return this.edgeMatrix[nV1][nV2];
	    }

	    return -1;
	  }

	  public boolean AddVertex(Vertex v)
	  {
	    if (v != null)
	    {
	      this.vertexList.add(v);
	      return true;
	    }

	    return false;
	  }

	  public boolean AddEdge(int nV1, int nV2, int nWeight)
	  {
	    if ((nWeight > 0) && (nV1 < this.edgeMatrix.length) && (nV2 < this.edgeMatrix.length))
	    {
	      this.edgeMatrix[nV1][nV2] = nWeight;
	      this.nEdgeNum++;
	      return true;
	    }

	    return false;
	  }

	  public boolean RemoveEdge(int nV1, int nV2)
	  {
	    if ((nV1 < this.edgeMatrix.length) && (nV2 < this.edgeMatrix.length))
	    {
	      this.edgeMatrix[nV1][nV2] = 0;
	      this.nEdgeNum--;
	      return true;
	    }

	    return false;
	  }
	  
	  //找出nSource和nTarget之间所有的路径
	  public boolean FindAllPath(int nSource, int nTarget,ArrayList<Path> pathList)
	  {
	    if(nSource<0||nTarget<0)
	    {
	    	return false;
	    }
		  
		if(pathList==null)
	    {
	    	pathList=new ArrayList<Path>();
	    }
	    else
	    {
	    	pathList.clear();
	    }
		if (!(isConnected(nSource, nTarget)))
	    {
	      System.out.println("起始点和终点之间不连通");
	      return false;
	    }
	  
	    //初始化
	    for(int i=0;i<vertexList.size();i++)
	    {
	    	ArrayList<Integer> tempArray=new ArrayList<Integer>();
	    	for(int j=0; j<vertexList.size();j++)
	    	{
	    		tempArray.add(0);
	    	}
	    	vertexList.get(i).visitedVertexIdList=tempArray;
	    }
	        
	    FindPath(nSource, nTarget,pathList);
	    return true;
	  }


	  private void FindPath(int nSource, int nTarget,ArrayList<Path> pathList)
	  {
	    Stack<Integer> stackPath = new Stack<Integer>();
	    (this.vertexList.get(nSource)).bVisited = true;
	    stackPath.push(nSource);

	    while (!(stackPath.isEmpty()))
	    {
	      int nAdj = GetAdjacentUnVisitedVertex((stackPath.peek()).intValue(), stackPath);
	      if (nAdj < 0)
	      {
	        ArrayList<Integer> tempArray = new ArrayList<Integer>();
	        for (int i = 0; i < this.vertexList.size(); ++i)
	        {
	          tempArray.add(0);
	        }
	        (this.vertexList.get(stackPath.peek())).visitedVertexIdList = tempArray;
	        stackPath.pop();
	      }
	      else
	      {
	        stackPath.push(nAdj);
	        
		     if ((stackPath.isEmpty()) || (nTarget != (stackPath.peek()).intValue()))
			        continue;
			      (this.vertexList.get(nTarget)).bVisited = false;
			      //找出所有路径
			      //this.PrintStack(stackPath);
			      Path path=new Path();
			      path.listSerialVertexId=ConvertStackToList(stackPath);
			      pathList.add(path);
			      stackPath.pop();
	      }

	    }
	  }

	  public boolean isConnected(int nSource, int nTarget)
	  {
	    if(nSource<0||nTarget<0)
	    {
	    	return false;
	    }
		 
		 ArrayList<Integer> queue = new ArrayList<Integer>();
		 ArrayList<Integer> bVisited = new ArrayList<Integer>();
		 queue.add(Integer.valueOf(nSource));
		    while (!(queue.isEmpty()))
		    {
		      for (int i = 0; i < this.vertexList.size(); ++i)
		      {
		        if ((this.edgeMatrix[nSource][i] <= 0) || (bVisited.contains(Integer.valueOf(i))))
		          continue;
		        queue.add(i);
		      }
	
		      if (queue.contains(Integer.valueOf(nTarget)))
		      {
		        return true;
		      }
	
		      bVisited.add((Integer)queue.get(0));
		      queue.remove(0);
		      if (queue.isEmpty())
		        continue;
		      nSource = ((Integer)queue.get(0)).intValue();
		    }
	
		    return false;
	  }

	  private int GetAdjacentUnVisitedVertex(int nParent, Stack<Integer> stack)
	  {
	    if(nParent<0||stack==null)
	    {
	    	return -1;
	    }
		  
		for (int i = 0; i < this.vertexList.size(); i++)
	    {
	    	if(edgeMatrix[nParent][i]>0&&this.vertexList.get(nParent).visitedVertexIdList.get(i)==0&&!stack.contains(i))
	    	{
	    		this.vertexList.get(nParent).visitedVertexIdList.set(i, 1);
	    		return i;
	    	}

	    }

	    return -1;
	  }
	  
	  private void PrintStack(Stack<Integer> stack)
	  {
		  System.out.print("找到一条路径:");
		  for(Integer n:stack)
		  {
			  System.out.print(n);
			  if(n!=stack.peek())
			  {
				  System.out.print("-->");
			  }
			  else
			  {
				  System.out.println(";");
			  }
		  }
	  }
	  
	  private ArrayList<Integer> ConvertStackToList(Stack<Integer> stack)
	  {
		  ArrayList<Integer> tempArray=new ArrayList<Integer>();
		  for(Integer n:stack)
		  {
			  tempArray.add(n);
		  }
		  return tempArray;
	  }
	  
	  public void DisplayPath(ArrayList<Path> pathList)
	  {
		  
		  if(pathList.size()<=0)
		  {
			  System.out.println("没有路径");
		  }
		  for(Path path:pathList)
		  {
			  System.out.print("输出一条路径:");
			  for(Integer n:path.listSerialVertexId)
			  {
				  System.out.print(vertexList.get(n).oValue);
				  if(n!=path.listSerialVertexId.get(path.listSerialVertexId.size()-1))
				  {
					  System.out.print("-->");
				  }
				  else
				  {
					  System.out.println(";");
				  }
			  }
		  }
	  }
	  
	  //计算路径的长度
	  public int GetPathDistance(Path path)
	  {
		  if(path!=null)
		  {
			  int nDistance=0;
			  for(int i=0;i<path.listSerialVertexId.size()-1;i++)
			  {
				  nDistance+=edgeMatrix[path.listSerialVertexId.get(i)][path.listSerialVertexId.get(i+1)];
			  }
			  return nDistance;
		  }
		  else
		  {
			  return -1;
		  }
	  }
	  

}