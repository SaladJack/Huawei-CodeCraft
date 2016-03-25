package com.routesearch.route;

import java.util.ArrayList;
import java.util.Collections;

import com.filetool.model.Edge;
import com.filetool.model.Graph;
import com.filetool.model.Path;

public class Route {
	/**
	 * 你需要完成功能的入口
	 * 
	 * @author Yin.Fan
	 * @since 2016-3-4
	 * @version V1
	 */
	public static String searchRoute(String graphContent, String condition) {
		final String NO_ANSWER = "NA";
		ArrayList<Integer> arrayVertexId = new ArrayList<Integer>();
		ArrayList<Edge> arrayEdge = new ArrayList<Edge>();
		// 解析图像信息
		if (!ResolveGraphContent(graphContent, arrayVertexId, arrayEdge)) {
			return NO_ANSWER;
		}// 进行条件判断，返回NA？
		int nVertexNum = arrayVertexId.size();// 图中顶点的数量
		// 解析题目条件
		String[] arrayCondition = condition.split(",");
		if (arrayCondition.length < 3) {
			return NO_ANSWER;
		}
		int nTopoSourceId = Integer.parseInt(arrayCondition[0]);// 在拓扑结构中的路径起点
		int nTopoDestId = Integer.parseInt(arrayCondition[1]);// 在拓扑结构中的路径终点
		int nSerialSourceId = arrayVertexId.lastIndexOf(nTopoSourceId);// 在邻接矩阵中起点的标号
		int nSerialDestId = arrayVertexId.lastIndexOf(nTopoDestId);// 在邻接矩阵中终点的标号

		ArrayList<Integer> fixedVertexList = new ArrayList<Integer>();// 必须经过的顶点列表
		String fixedPointList = arrayCondition[2].replace("\n", "");// 过定点的列表,去除换行符
		String arrayFixedPoint[] = fixedPointList.split("\\|");
		for (String strFixedPoint : arrayFixedPoint) {
			int nFixedPoint = Integer.parseInt(strFixedPoint);
			fixedVertexList.add(nFixedPoint);
		}

		Graph graph = new Graph(nVertexNum);
		graph.Init(arrayVertexId, arrayEdge);
		ArrayList<Path> allPathList = new ArrayList<Path>();// 从起点到终点在图中所有的路径
		if (!graph.FindAllPath(nSerialSourceId, nSerialDestId, allPathList)) {
			return NO_ANSWER;
		}
		ArrayList<Path> filterPathList = new ArrayList<Path>();// 过定点的路径集合
		for (Path path : allPathList) {
			if (path.ContainFixedVertexList(fixedVertexList)) {
				filterPathList.add(path);
			}
		}
		for (Path path : filterPathList) {
			path.nPathDistance = graph.GetPathDistance(path);
		}
		Path shortestPath = filterPathList.get(0);
		for (Path path : filterPathList) {
			if (path.nPathDistance < shortestPath.nPathDistance) {
				shortestPath = path;
			}
		}
		String strShortestPath = shortestPath.GetPathInTopo(arrayEdge);
		return strShortestPath;

	}

	// 解析图像信息
	private static boolean ResolveGraphContent(String graphContent,
			ArrayList<Integer> arrayVertexId, ArrayList<Edge> arrayEdge) {
		if (arrayVertexId == null) {
			arrayVertexId = new ArrayList<Integer>();
		} else {
			arrayVertexId.clear();
		}
		if (arrayEdge == null) {
			arrayEdge = new ArrayList<Edge>();
		} else {
			arrayEdge.clear();
		}

		String[] groupEdgeInfo = graphContent.split("\n");

		for (String strEdgeInfo : groupEdgeInfo) {
			String[] unit = strEdgeInfo.split(",");
			if (unit.length < 4) {
				return false;
			}
			Integer nSource = Integer.parseInt(unit[1]);
			Integer nDest = Integer.parseInt(unit[2]);
			if (!arrayVertexId.contains(nSource)) {
				arrayVertexId.add(nSource);
			}
			if (!arrayVertexId.contains(nDest)) {
				arrayVertexId.add(nDest);
			}

			Edge tempEdge = new Edge();
			tempEdge.strSerialNo = unit[0];
			tempEdge.nSourceIdInTopo = Integer.parseInt(unit[1]);
			tempEdge.nDestIdInTopo = Integer.parseInt(unit[2]);
			tempEdge.nWeight = Integer.parseInt(unit[3]);
			if (!CheckEdgeInfoData(tempEdge)) {
				return false;
			}
			arrayEdge.add(tempEdge);

		}

		Collections.sort(arrayVertexId);// 升序排序
		return true;
	}

	// 检验输入数据的合法性
	private static boolean CheckEdgeInfoData(Edge edge) {
		if (edge != null) {
			if (edge.nSourceIdInTopo < 0 || edge.nDestIdInTopo < 0
					|| edge.nWeight < 0) {
				return false;
			} else {
				return true;
			}
		} else {
			return false;
		}
	}

}