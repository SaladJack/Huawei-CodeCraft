package com.filetool.model;

import java.util.ArrayList;

public class Path {
	public ArrayList<Integer> listSerialVertexId;// 该路径上的顶点
	public int nPathDistance;// 该路径的总长度

	public Path() {
		listSerialVertexId = new ArrayList<Integer>();
		nPathDistance = Integer.MAX_VALUE;// 路径长初始认为无穷远
	}

	// 获得该路径在拓扑结构中表示
	public String GetPathInTopo(ArrayList<Edge> edgeList) {
		if (edgeList != null && edgeList.size() > 0) {
			ArrayList<String> edgeIdList = new ArrayList<String>();
			for (int i = 0; i < this.listSerialVertexId.size() - 1; i++) {
				for (Edge edge : edgeList) {
					if (listSerialVertexId.get(i) == edge.nSourceIdInMatrix
							&& listSerialVertexId.get(i + 1) == edge.nDestIdInMatrix) {
						edgeIdList.add(edge.strSerialNo);
						break;
					}
				}
			}
			String strPathInTopo = "";
			for (String strEdgeId : edgeIdList) {
				strPathInTopo += strEdgeId;
				if (strEdgeId != edgeIdList.get(edgeIdList.size() - 1)) {
					strPathInTopo += "|";
				}
			}
			return strPathInTopo;
		} else {
			return "";
		}

	}

	// 路径是否过定点
	public boolean ContainFixedVertexList(ArrayList<Integer> fixedVertexList) {
		if (fixedVertexList != null) {
			ArrayList<Integer> queue = new ArrayList<Integer>();
			for (Integer n : this.listSerialVertexId) {
				if (fixedVertexList.contains(n)) {
					queue.add(n);
				}
			}
			if (queue.size() == fixedVertexList.size()) {
				return true;
			} else {
				return false;
			}
		} else {
			return false;
		}
	}

}