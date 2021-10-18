import styled from 'styled-components';

export const Container = styled.div`
  display: flex;
  flex-direction: column;
  flex-wrap: wrap;
  align-items: center;
  padding: 20px 0;
  max-width: 100%;
  overflow-x: auto;
  
  ::-webkit-scrollbar {
    width: 5px;
    height: 5px;
  } 
  ::-webkit-scrollbar-track {
    background: #ebedf0;
  }
  ::-webkit-scrollbar-thumb {
    background: #ccc;
  }
`;

export const FlexContainer = styled.div`
  display: flex; 
  align-items: center;
  font-size: 10px;
  margin-top: ${props => props.legend ? '10px' : 0} 
`;

export const ColumnsContainer = styled.div`
  display: flex;
  margin-left: 7px;
  position: relative;
  text-transform: capitalize;
  padding-top: 14px;
`;

export const WeekContainer = styled.div`
  height: 98px;
  text-transform: capitalize;
  margin-top: 14px;
`;

export const WeekLabel = styled.div`
  display: flex;
  align-items: center;
  height: 14px;
`;

export const BoxContainer = styled.div`
  display: flex;
  flex-direction: column;
  flex-wrap: wrap;
`;